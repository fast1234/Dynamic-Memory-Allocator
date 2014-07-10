/* This code runs on a 32 bit processor.

This is a code of a simple allocator based on the concept of explict free list with boundary tag colaceing.
    The Explict free list is advantageous in case of throughput. Since now we are jumping only among the free list and not even checking the allocated block.
 This is achieved by taking a linked list, in which there are a pointers for next and prvious free blocks.

 Each block has header and footer of the form that the least significant bit of header and footer saves the status of the allocation of the current block.
 The list has the following form:

 1)First there is a padding of 4 bytes for allignment purposes.
 2)Then there is a header.
 3)Followed by header of 4 bytes, there is a 4 byte next block status storage, and a 4 byte previous block status storage
 4)We store data after that followed by footer pointer.
 5)And so on we continue with more blocks


 Intial Block Size (minimum) is 24 bytes
 Explicit list Structure with pointers:
 prev - previous free block
 next - next free block

 The allocated prologue and epilogue blocks are overhead that
 eliminate edge conditions during coalescing.
*/

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"


/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Coders",
    /* First member's full name */
    "Yash Kumar Jain",
    /* First member's email address */
    "201201080@daiict.ac.in",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


/* Basic constants and macros */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define ALIGNMENT   2*(WSIZE)		/* Alignment requirement (8 bytes)*/
#define OVERHEAD 	4*(WSIZE)  	/* defining overhead by default to be 16 bytes*/
#define BLKSIZE     6*(WSIZE)  	/* The minimum block size is taken to be 24 */

/* Rounding up to nearest multiple of 8 */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/*Max value of 2 values*/
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and set allocated bit to 1 */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define SIZE(p) (GET(p) & ~0x7)   //size is calculated ignoring the 3 least significant digits
#define GET_SIZE(p)  (GET(HDRP(p)) & ~(DSIZE - 1))
#define GET_ALLOC(p) (GET(HDRP(p)) & 0x1)   //tells that block is allocated or not

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(bp) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(bp))
#define PREV_BLKP(bp)  ((char *)(bp) - SIZE((char *)(bp) - DSIZE))

/*Given a base pointer ,  calculate the next and prev pointers of start of next block and previous blocks respectively */
#define NEXT_PTR(bp)  (*(char **)(bp + WSIZE))
#define PREV_PTR(bp)  (*(char **)(bp))

/* Sets header, footer, prev and next of block */
#define SET_HDRP(bp, val) (PUT(HDRP(bp), (int)val))
#define SET_FTRP(bp, val) (PUT(FTRP(bp), (int)val))
#define SET_NEXT(bp, qp) (NEXT_PTR(bp) = qp)
#define SET_PREV(bp, qp) (PREV_PTR(bp) = qp)

// Uptil here we have defiened all macros

// heaplistp always points to tahe start of the heap
static char *heap_listp = 0;
// Global list pointer
static char *listp = 0;
//static char *ro;



// Declaration of all function prototypes
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


static void mm_add(void *bp);
static void mm_delete(void *bp);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);
static void check_contigous(void *bp);
void check_is_next_ptr_pointing_to_free(void *bp);
void freelist_freeblock(void *bp);
/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int mm_init(void) {

    /* Create the initial empty heap and returns -1 if unable to get heap space*/
    if ((heap_listp = mem_sbrk(2*BLKSIZE)) ==(void *)-1)
        return -1;

    PUT(heap_listp, 0); 								/* alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(BLKSIZE, 1)); 		/* prologue header */
    PUT(heap_listp + (2*WSIZE), 0); 					/* prev pointer */
    PUT(heap_listp + (3*WSIZE), 0); 					/* next pointer */
    PUT(heap_listp + BLKSIZE, PACK(BLKSIZE, 1)); 		/* prologue footer */
    PUT(heap_listp+  BLKSIZE + WSIZE, PACK(0, 1)); 		/* epilogue header */
    listp = heap_listp + DSIZE;
    /* Extend the empty heap with a free block of BLKSIZE bytes */
    if (extend_heap(BLKSIZE) == NULL){
        return -1;
    }
    return 0;
}

/* Malloc original block calling find fit function to allocate*/


void *mm_malloc(size_t size) {
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests */
    if (size <= 0){
        return NULL;
    }

    /* least size is 24 bytes stored in BLKSIZE */
    asize = MAX(ALIGN(size) + DSIZE, BLKSIZE);

    /*we call findfit to traverse through the free list to find a fit for a malloc call*/

    if ((bp = find_fit(asize))) {
        place(bp, asize);
        return bp;
    }

    /* If unable to fetch a fit then simply extend a size */

    extendsize = MAX(asize,CHUNKSIZE);
    //extendsize = (asize);// first we were trying to increase  size as the requested size

    /* return NULL if unable to get additional space */
    if ((bp = extend_heap(extendsize)) == NULL) {
        return NULL;
    }
    /* place block and return bp */
    place(bp, asize);
    return bp;
}

/*
  Marks this block as free. Calls
  coalesce to merge with adjacent free blocks
  if any, then inserts the returned
  free block into the tree of free blocks
 */

void mm_free(void *bp){
    size_t size;
    /* just return if the pointer is NULL */
    if (bp == NULL)
        return;


    size = GET_SIZE(bp);

    // Then we may coalese the block
    SET_HDRP(bp, PACK(size, 0));
    SET_FTRP(bp, PACK(size, 0));
    coalesce(bp);
}


/**
  Return a block of size with its newsize
  that preserves all the data from the
  payload of the block bp.
 */

void *
mm_realloc(void *ptr, size_t size){
    if(size <= 0){
        mm_free(ptr);
        return NULL;
    }

    if(ptr == NULL){
        ptr = mm_malloc(size);
        return ptr;
    }

    if(size > 0){
        size_t currentsize = GET_SIZE(ptr);
        size_t newsize = ALIGN(size + OVERHEAD);

        if(newsize <= currentsize){

            /*void *newbp ;
            if ((currentsize - newsize) >= BLKSIZE) {
                SET_HDRP(ptr, PACK(newsize, 1));
                SET_FTRP(ptr, PACK(newsize, 1));
                newbp=ptr;
                mm_remove(ptr);
                ptr = NEXT_BLKP(ptr);
                SET_HDRP(ptr, PACK(currentsize-newsize, 0));
                SET_FTRP(ptr, PACK(currentsize-newsize, 0));
                coalesce(ptr);
                return newbp;
            }
            else {*/
                //return ptr;
            //}
            return ptr;

        } /* Defining the code if new size is greater than the current */
        else {
            size_t next_alloc = GET_ALLOC(NEXT_BLKP(ptr));
            size_t csize;
            size_t asize;
            /* next block is free and the size of the two blocks is greater than or equal the new size  */

            if(!next_alloc && ((csize = currentsize + GET_SIZE(NEXT_BLKP(ptr)))) >= newsize){
                mm_delete(NEXT_BLKP(ptr));
                SET_HDRP(ptr, PACK(csize, 1));
                SET_FTRP(ptr, PACK(csize, 1));
                return ptr;
            }
            /* if bp is the last block before epilogue */
            else if(GET_SIZE(NEXT_BLKP(ptr)) == 0){
                csize = newsize - currentsize;
                void *temp = extend_heap(csize);
                asize = currentsize + GET_SIZE(temp);
                SET_HDRP(ptr, PACK(asize, 1));
                SET_FTRP(ptr, PACK(asize, 1));
                return ptr;
            }
            /* next block is free and the block is the last block before the epilogue */

            else if(!next_alloc && ((GET_SIZE(NEXT_BLKP(NEXT_BLKP(ptr)))) == 0)){
                csize = newsize - currentsize + GET_SIZE(NEXT_BLKP(ptr));
                void *temp = extend_heap(csize);
                asize = currentsize + GET_SIZE(temp);
                SET_HDRP(ptr, PACK(asize, 1));
                SET_FTRP(ptr, PACK(asize, 1));
                return ptr;
            }

           /* otherwise there is no choice left instead to increase the heap size */

            else {
                void *newbp = mm_malloc(newsize);
                place(newbp, newsize);
                memcpy(newbp, ptr, newsize);
                mm_free(ptr);
                return newbp;
            }
        }
    }else{
        return NULL;
    }
}



/*
  coalesce - boundary tag coalescing. Return ptr to coalesced block
  Removes adjacent blocks from the free list if either one or both are free.
  Merges block bp with these free adjacent blocks and inserts it onto list.

 */
static void *coalesce(void *bp){
    size_t prev_alloc;
    prev_alloc = GET_ALLOC(PREV_BLKP(bp)) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(NEXT_BLKP(bp));
    size_t size = GET_SIZE(bp);
    if (prev_alloc && next_alloc) {                 /* when both are allocated */
        //do nothing
    }/* when prev block is free */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
        mm_delete(bp);
        SET_HDRP(bp, PACK(size, 0));
        SET_FTRP(bp, PACK(size, 0));
    }

    /* when next block is free */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(NEXT_BLKP(bp));
        mm_delete(NEXT_BLKP(bp));
        SET_HDRP(bp, PACK(size, 0));
        SET_FTRP(bp, PACK(size, 0));
    }/* when both blocks are free */
    else if (!prev_alloc && !next_alloc) {
        size += GET_SIZE(PREV_BLKP(bp)) + GET_SIZE(NEXT_BLKP(bp));
        mm_delete(PREV_BLKP(bp));
        mm_delete(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        SET_HDRP(bp, PACK(size, 0));
        SET_FTRP(bp, PACK(size, 0));
    }/* lastly insert bp into free list and return bp */
    mm_add(bp);

    //if ((ro > (char *)bp) && (ro < NEXT_BLKP(bp)))
    //ro = bp;
    return bp;
}

/*
  extend_heap - Extend heap with free block and return its block pointer
  Allocates a new free block of size which is a multiple of 16 immediately after
  the last block. Merges this new block with the last block if that block is free.
  Rewrites an epilog block after the new block.
 */

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;


    /* call for more memory space */
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return (NULL);

    /* Initialize free block header/footer and the epilogue header */
    SET_HDRP(bp, PACK(size, 0));         /* free block header */
    SET_FTRP(bp, PACK(size, 0));         /* free block footer */
    SET_HDRP(NEXT_BLKP(bp), PACK(0, 1)); /* new epilogue header */

    /* coalesce bp with next and previous blocks */
    return coalesce(bp);
}

/**
  Search through the list for free blocks whose size is >= asize remove this block from the
  list and return it.  If no block is found, return null.
  First Fit Algorithm - Find a first fit for a block with asize bytes
  where asize = a size block from the free list
   and bp = pointer to best fit block
 */
static void *find_fit(size_t asize){
    void *bp;
    /* for loop through list to find first fit */
    for (bp = listp; GET_ALLOC(bp) == 0; bp = NEXT_PTR(bp))
    {
        if (asize <= (size_t)GET_SIZE(bp)){

        return bp;
        }
    }


    return NULL;     /* returns NULL if can't find it in the list */


  /*char *old = ro;
  /*for ( ; GET_SIZE(HDRP(ro)) > 0; ro = NEXT_PTR(ro))
    if (!GET_ALLOC((ro)) && (asize <= GET_SIZE((ro))))
      return ro;

  /*for (ro = listp; ro < old; ro = NEXT_BLKP(ro))
    if (!GET_ALLOC((ro)) && (asize <= GET_SIZE((ro))))
      return ro;

  return NULL;*/

}


/*
  Place block of asize bytes at start of free block bp and split if remainder would be at least minimum block size
  the requested size of free block
 */
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(bp);

    if ((csize - asize) >= BLKSIZE) {
        SET_HDRP(bp, PACK(asize, 1));
        SET_FTRP(bp, PACK(asize, 1));
        mm_delete(bp);
        bp = NEXT_BLKP(bp);
        SET_HDRP(bp, PACK(csize-asize, 0));
        SET_FTRP(bp, PACK(csize-asize, 0));
        coalesce(bp);
    }
    else {
        SET_HDRP(bp, PACK(csize, 1));
        SET_FTRP(bp, PACK(csize, 1));
        mm_delete(bp);
    }
}

/* Adds this block to the free list of free blocks.bp is the pointer to a block that is already marked free.
 */
static void mm_add(void *bp){
    /* set bp next to listp */
    SET_NEXT(bp, listp);
    /* set prev listp to bp */
    SET_PREV(listp, bp);
    /* set prev bp to NULL */
    SET_PREV(bp, NULL);
    /* set start of list to bp */
    listp = bp;
}

/* Removes this block from the list of free blocks. bp is the  pointer to a block that is on the list of free blocks.
 */
static void mm_delete(void *bp){
    /* if prev bp, then set it's next to bp next */
    if (PREV_PTR(bp)){
        SET_NEXT(PREV_PTR(bp), NEXT_PTR(bp));
    }
    else{	/* set listp to bp's next */
        listp = NEXT_PTR(bp);
    }
    /* set prev of next after bp to prev of bp */
    SET_PREV(NEXT_PTR(bp), PREV_PTR(bp));
}




/*
 * The remaining routines are heap consistency checker routines.
 */
/*
	check if two contigous blocks are free then prints error statement
*/
void check_contigous(void *bp)
 {
    		for (bp = listp; GET_ALLOC(bp) == 0; bp = NEXT_PTR(bp))
        	{
            		if((GET_ALLOC((bp)==0)) &&(GET_ALLOC((NEXT_PTR(bp)))==0))
                		printf("found 2 contigous block at pointer %p\n",bp);

            	}
        }

/*
	check if the free blocks exist in free list or not. If not then prints Error not in free list.
*/

void check_freelist_freeblock(void *bp)

 {	void *bp1;int flag=0;
        for(bp1 = listp;GET_ALLOC(bp1) == 0; bp1 = NEXT_BLKP(bp1)){
            flag=0;
            if(GET_ALLOC(bp1)==0) {
				for (bp = listp; GET_ALLOC(bp) == 0; bp = NEXT_PTR(bp))
        		{
                    if(bp1==bp){
                        flag++;
                       break;
                    }


            		}
                if(flag==0){
                    printf("Error:free block not in free list");
                }

		}
			}
	}    			




/* checks that is next pointer points to free block 
if not then prints the error 
*/
void check_is_next_ptr_pointing_to_free(void *bp)
 	{
    			for (bp = listp; GET_ALLOC(bp) == 0; bp = NEXT_PTR(bp))
        		{
            			if(GET_ALLOC(NEXT_PTR(bp))==1)
				{	
					printf("Next pointer is not pointing to free block.\n ");
			
				}

            		}
        }



/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
 static void
checkblock(void *bp)
{

    if ((uintptr_t)bp % (DSIZE))
        printf("Error: %p is not 8 bytes aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}


/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency.
 */
void
checkheap(bool verbose)
{
    void *bp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
        !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
        printf("Bad epilogue header\n");

	 check_is_next_ptr_pointing_to_free(bp);
	 
	 check_contigous(bp);

     check_freelist_freeblock(bp);
}


/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp)
{
    bool halloc, falloc;
    size_t hsize, fsize;

    checkheap(false);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: end of heap\n", bp);
        return;
    }

    printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
        hsize, (halloc ? 'a' : 'f'),
        fsize, (falloc ? 'a' : 'f'));
}


/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */


