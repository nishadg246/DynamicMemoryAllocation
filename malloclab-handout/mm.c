/*
 * mm.c
 *
 * My malloc implementation uses 8 segregated lists assigned to
 * different size classes. The minimum block size is 16 to account
 * for 4 bytes headers and footers and since the heap is 2^32
 * it can be represented in 4 bytes so we need 4 byte "pointers"
 * in our doubly linked free lists (next and prev pointers).
 *
 * The header and footer store the size and since it is 8 byte aligned
 * we use the last bit of the header and footer to store the allocation
 * status for the block (1 for allocated and 0 for free).
 *
 * Our freelists is maintained by 8 pointers corresponding to the front
 * of each of the 8 freelists. When we insert we put it in its correct
 * spot in ascending order. When we delete we rewire the pointers around 
 * the block we remove.
 *
 * Extending the heap requires changing our epilogue block representing
 * the end of our "extended" heap. And we always have a prologue block
 * which we place in our init function
 *
 * Now when we want to allocate memory we first check the freelist for
 * a block that fits our request and if it exists we take it off the freelist
 * and "hand" it to the user. If it isnt in the free list, we extend the
 * heap and now we will have sufficient room to give space to the user
 *
 * Finally when users want to freeblocks, we reestablish our headers and
 * footer scheme and return it to the free list
 *
 * Important housekeeping is coalescing which reduces fragmentation by
 * ensuring that if two adjacent blocks are free we merge them into one.
 * 
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"


#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

#ifdef DRIVER

#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

#define ALIGNMENT 8

// round
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

// constants
#define WSIZE       4   /* word size (bytes) */  
#define DSIZE       8   /* doubleword size (bytes) */
#define CHUNKSIZE   (1<<8)
#define MINIMUM    16

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// pack size and alloc bit 
#define PACK(size, alloc)  ((size) | (alloc))

// get and put 4 bytes or 8 bytes
#define GET4(p)       (*(unsigned*)(p))
#define PUT4(p, val)  (*(unsigned*)(p) = (unsigned)(size_t)(val))

#define GET8(p)       (*(size_t *)(p))
#define PUT8(p, val)  (*((size_t *)(p)) = (size_t)(val))

// size and alloc status
#define GET_SIZE(p)  (GET4(p) & ~0x7)
#define GET_ALLOC(p) (GET4(p) & 0x1)

// address of header and footer
#define HDRP(bp)       ((char*)(bp) - WSIZE)
#define FTRP(bp)       ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// address of next block and prev block
#define NEXT_BLKP(bp)  ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char*)(bp) - GET_SIZE(HDRP(bp) - WSIZE))

// next and prev in free list
#define NEXT(bp)    ((char*) ((char*)(bp) + WSIZE))
#define PREV(bp)    ((char*) ((char*)(bp)))



static char *heap_start;
static char *heap_list;


static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void insert(void *bp); /* Linked list function */
static void delete(void *bp); /* Linked list function */
static void *coalesce(void* bp);


/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) { ///
    // space for 8 pointers corresponding to freelists
    if ((heap_list = mem_sbrk(8 * DSIZE)) == NULL)
        return -1;

    // prologue block and epilogue
    if ((heap_start = mem_sbrk(4 * WSIZE)) == NULL)
        return -1;
    // alignment
    PUT4(heap_start, 0);
    // header
    PUT4(heap_start + WSIZE, PACK(DSIZE, 1));
    // footer
    PUT4(heap_start + (2 * WSIZE), PACK(DSIZE, 1));
    // epilogue
    PUT4(heap_start + (3 * WSIZE),PACK(0, 1));

    // set all free lists to NULL
    PUT8(heap_list, (size_t) NULL);
    PUT8(heap_list+1*DSIZE, (size_t) NULL);
    PUT8(heap_list+2*DSIZE, (size_t) NULL);
    PUT8(heap_list+3*DSIZE, (size_t) NULL);
    PUT8(heap_list+4*DSIZE, (size_t) NULL);
    PUT8(heap_list+5*DSIZE, (size_t) NULL);
    PUT8(heap_list+6*DSIZE, (size_t) NULL);
    PUT8(heap_list+7*DSIZE, (size_t) NULL);

    // make empty space
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;

    return 0;
}


/* 
 * getlist - Designates which list this size
 *           corresponds to
 */
static size_t getlist(size_t size){
    size_t ind;
    if(size<20){
        ind=0;
    }else if(size<49){
        ind=1;
    }else if(size<88){
        ind=2;
    }else if(size<176){
        ind=3;
    }else if(size<352){
        ind=4;
    }else if(size<700){
        ind=5;
    }else if(size<1400){
        ind=6;
    }else{
        ind=7;
    }
    return ind;
}

/* 
 * rightsizeclass - Checks if size corresponds to free
 *           list ind
 */
static int rightsizeclass(size_t ind, size_t size){
    if(ind==0){
        return size<20;
    }else if(ind==1){
        return size>=20 && size<49;
    }else if(ind==2){
        return size>=49 && size<88;
    }else if(ind==3){
        return size>=88 && size<176;
    }else if(ind==4){
        return size>=176 && size<352;
    }else if(ind==5){
        return size>=352 && size<700;
    }else if(ind==6){
        return size>=700 && size<1400;
    }else{
        return size>=1400;
    }
}

// get next pointer from block ( accounting for NULLs )
static void* nextpointer(void* point){
    return GET4(NEXT(point)) ? (char*)(0x800000000) + GET4(NEXT(point)) : NULL;
}

// get prev pointer from block ( accounting for NULLs )
static void* prevpointer(void* point){
    return GET4(PREV(point)) ? (char*)(0x800000000) + GET4(PREV(point)) : NULL;
}

/* 
 * insert - Inserts block into proper free list
 *          in increasing order of size
 */
static void insert(void* bp){
    // get size and corresponding free list
    size_t size = GET_SIZE(HDRP(bp));
    char* loc = heap_list+getlist(size)*DSIZE;
    char* freelist = (char*)(GET8(loc));

    // before and after insertion point
    char* after = freelist;
    char* before = NULL;

    // loop until proper location is found
    while((after!=NULL) && (size > GET_SIZE(HDRP(after)))){
        before=after;
        after = nextpointer(after);
    }
    if(after!=NULL){ // not at end of list
        // not at front of list
        if(before!=NULL){
            PUT4(NEXT(bp),after);
            PUT4(PREV(after),bp);
            PUT4(PREV(bp),before);
            PUT4(NEXT(before),bp);
        }else{
            PUT4(NEXT(bp),after);
            PUT4(PREV(after),bp);
            PUT4(PREV(bp),NULL);
            PUT8(loc,bp); 
        }
    }else{ // at end of list
        if(before!=NULL){
            PUT4(NEXT(bp),NULL);
            PUT4(PREV(bp),before);
            PUT4(NEXT(before),bp);
        }else{
            PUT4(NEXT(bp),NULL);
            PUT4(PREV(bp),NULL);
            PUT8(loc,bp);
        }
    }
}

/* 
 * extend_heap - Increases size of heap
 *          and places block on freelist
 */
static void *extend_heap(size_t words) //
{
    char *bp;
    size_t size;

    // even amount of words
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    // don't increment less than MIN
    if(size<MINIMUM){
        size=MINIMUM;
    }

    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    // make new free block and insert it
    PUT4(HDRP(bp), PACK(size, 0));
    PUT4(FTRP(bp), PACK(size, 0));
    insert(bp);

    // make new epilogue block
    PUT4(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
    
    return coalesce(bp);                                          
}

/*
 * malloc - give user a pointer to block of size "size"
 */
void *malloc (size_t size) {

    size_t newsize;
    size_t extend;
    char* search=NULL;

    if(!size){
        return NULL;
    }

    // because header and footer take room
    newsize=MAX(ALIGN(size)+2*WSIZE,MINIMUM);

    // look for a fit on the free list
    if((search=find_fit(newsize))!=NULL){
        place(search, newsize);
        return search;
    }

    // extend if it cannot be found on free list
    extend=MAX(newsize,CHUNKSIZE);
    if((search=extend_heap(extend/WSIZE))==NULL){
        return NULL;
    }

    place(search,newsize);
    return search;
}

/*
 * find_onlist - look on list index for block of proper size
 */
static void *find_onlist(size_t size,size_t index){
    char* search = (char *) GET8(heap_list+index*DSIZE);
    while(search != NULL){
        if(size<=GET_SIZE(HDRP(search))){
            break;
        }
        search = nextpointer(search);
    }
    return search; 
}

/*
 * find_fit - search all freelists of blocks of size
            greater than or equal to size
 */
static void *find_fit(size_t size){
    void* bp=NULL;
    size_t ind = getlist(size);
    for (; ind < 8; ind++) {
        if ((bp = find_onlist(size, ind)) != NULL){
            return bp;
        }
    }
    return NULL;
}

/*
 * delete - remove free block from free lists
 */
static void delete(void *bp)  {
    // get size and proper free list
    size_t size = GET_SIZE(HDRP(bp));
    char* loc=heap_list+getlist(size)*DSIZE;

    // see where in the free list this block is
    char* pre = prevpointer(bp);
    char* nex = nextpointer(bp);

    // adjust free list start pointer if necessary
    if(pre==NULL && nex==NULL){
        PUT8(loc,NULL);
    }else if(pre==NULL){
        PUT8(loc,nex);
        PUT4(PREV(nex),NULL);
    }else if(nex==NULL){
        PUT4(NEXT(pre),NULL);
    }else{
        PUT4(PREV(nex),pre);
        PUT4(NEXT(pre),nex);
    }
}

/*
 * place - designate a block to be allocated
        and if the remaining space in the block
        is enough to make a new block then make
        a new block with the remaining space
 */
static void place(void *bp, size_t asize)
{
    // get size and size of remainder
    size_t csize = GET_SIZE(HDRP(bp));   
    size_t scrap = csize-asize;
    delete(bp);
    // if big enough make a new block
    if (scrap >= MINIMUM) { 
        PUT4(HDRP(bp), PACK(asize, 1));
        PUT4(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT4(HDRP(bp), PACK(scrap, 0));
        PUT4(FTRP(bp), PACK(scrap, 0));
        insert(bp);
    }
    else {  // else just make the whole thing alloced
        PUT4(HDRP(bp), PACK(csize, 1));
        PUT4(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * coalesce - merge with blocks on the left or right
            that may be free to reduce internal frag
            and make on larger block
 */
static void *coalesce(void *bp) 
{
    // get allocation status of left and right
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // nothing can be done
    if (prev_alloc && next_alloc){
        return bp;
    }
    // merge with right
    if (prev_alloc && !next_alloc) {      /* Case 2 */
        delete(bp);
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT4(HDRP(bp), PACK(size, 0));
        PUT4(FTRP(bp), PACK(size,0));
        insert(bp);
        return bp;
    }
    // merge with left
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        delete(bp);
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp=PREV_BLKP(bp);
        PUT4(HDRP(bp), PACK(size, 0));
        PUT4(FTRP(bp), PACK(size,0));
        insert(bp);
        return bp;
    }
    // merge on both sides
    else {     
        delete(bp);
        delete(PREV_BLKP(bp));
        delete(NEXT_BLKP(bp));                              /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT4(HDRP(bp), PACK(size, 0));
        PUT4(FTRP(bp), PACK(size, 0));
        insert(bp);
        return bp;
        
    }
}

/*
 * free - designate block as free and put it in the freelist
            and coalesce with surrounding blocks
 */
void free(void *bp)
{
    if(bp!=NULL){
        size_t size = GET_SIZE(HDRP(bp));
        PUT4(HDRP(bp), PACK(size, 0));
        PUT4(FTRP(bp), PACK(size, 0));
        insert(bp);
        coalesce(bp);
    }
}

/*
 * realloc - reallocate
 */
void *realloc(void *oldptr, size_t size) {
    void *bp = oldptr;
    if(!size){
        mm_free(oldptr);
        return NULL;
    }
    if(bp==NULL){
        return mm_malloc(size);
    }
    size_t newsize = MAX(ALIGN(size)+DSIZE,MINIMUM);
    size_t csize = GET_SIZE(HDRP(bp));   
    int more = csize-newsize;
    if(more==0){
        return bp;
    }
    if(more>=0){
        if(csize-newsize<=MINIMUM){
            return bp;
        }
        PUT4(HDRP(oldptr), PACK(newsize, 1));
        PUT4(FTRP(oldptr), PACK(newsize, 1));
        PUT4(HDRP(NEXT_BLKP(oldptr)), PACK(more, 1));
        free(NEXT_BLKP(oldptr));
        return oldptr;
    }
    bp=malloc(size);
    if(size < csize){
        csize=size;
    }
    memcpy(bp,oldptr,csize);
    free(oldptr);
    return bp;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t sum = nmemb * size;
    
    char *bp = mm_malloc(sum);
    char *b = bp;
    // allocated zeros
    for (uint i = 0; i < nmemb; i++) {
        *b = 0;
        b = b + size;
    }

    return bp;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap - checks the "safety" of the heap to detect bugs in
                its architecture
 */
void mm_checkheap(int lineno) {
    char* point = heap_start + 2*DSIZE;
    int prevfree=-1;
    int count1=0;
    int count2=0;
    // check heap
    while (GET4(HDRP(point)) != 1){
        if(prevfree!=-1){
            if(prevfree && !GET_ALLOC(HDRP(point))){
                printf("two free blocks in a row");
            }
        }
        // no adjacent free blocks
        if(GET_ALLOC(HDRP(point))){
            prevfree=0;
        }else{
            prevfree=1;
            count1++;
        }
        // in heap and aligned
        if(!in_heap(point) || !aligned(point)){
            printf("not in heap or not aligned");
        }
        // ensures header and footer match
        if(GET4(HDRP(point))!=GET4(FTRP(point))){
            printf("header and footer dont match");
        }
        point=NEXT_BLKP(point);
        
    }

    // check each free list
    for(int i=0; i < 8; i++){
        char* freelist = (char *) GET8(heap_list+i*DSIZE);
        char* prev = NULL;
        while(freelist != NULL){
            if(GET_ALLOC(HDRP(freelist))){
                printf("alloc block in free list");
            }
            // doubly linked
            if(prev!=NULL){
                if(prevpointer(freelist)!=prev){
                    printf("next and prev pointer dont reciprotcate");
                }
            }
            if(!rightsizeclass(i,GET_SIZE(HDRP(freelist)))){
                printf("wrong size class");
            }
            if(!in_heap(freelist) || !aligned(freelist)){
            printf("not in heap or not aligned");
            }
            if(GET4(HDRP(freelist))!=GET4(FTRP(freelist))){
                printf("header and footer dont match");
            }
            prev= freelist;
            freelist = nextpointer(freelist);
            count2++;
        }
    }
    if(count2!=count1){
        printf("not all free blocks are in the free list");
    }


}
