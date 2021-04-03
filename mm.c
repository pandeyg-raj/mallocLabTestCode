/*
 * mm.c
 *
 * 
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

// Block alignment size
static const size_t ALIGNMENT = 16;

// Header/Footer alignment size
static const size_t WSIZE = 8;

// Pointer to Epilogue Hdr
static unsigned char *headPtr;

// Dynamic allocator functions
void* malloc(size_t size);
void free(void* ptr);
void* realloc(void *oldptr, size_t size);

//Segregated list
unsigned char *segList[10];
// Helper function to seg-list to define size classes
static int idxSegList(size_t blockLength);

//Slab allocator Head pointer to help traversal
unsigned char *freeListHeadPtr16;
unsigned char *freeListHeadPtr32;

// Doubly Linked list operation functions
static unsigned char *getFreeBlockPrevAddr(unsigned char *ptr);
static unsigned char *getFreeBlockNextAddr(unsigned char *ptr);
static void insertFreeBlock(void* ptr);
static void removeFreeBlock(void* ptr);

//Debug Utility functions
static bool in_heap(const void* p);
static bool aligned(const void* p);
static void traverse();
static void traverseAllSegList();
static void printHeap();
static void print16BHeap();
static void printBlockOnHeap(void* ptr);
static void searchHeapForEmptyBlocks(size_t size);
static void printOneWord(unsigned char * ptr);
static bool isPtrInside16BHeap(void *ptr);


// Helper functions
/*
 * Changes the last bit of size to allocation bit
 * for compact utilization of space
 */
inline static size_t packSizeAlloc(uint64_t size, uint64_t alloc) {
	return (size | alloc);
}

/*
 * Gets the Header value(size+allocationBit) from HeaderPointer
 */
inline static size_t getPtrValue(void *p) {
	return *(uint64_t*) p;
}

/*
 * Sets the Header value (size+allocationBit) to Header Pointer
 */
inline static void putPtrValue(void *p, size_t val) {
	*(uint64_t*) p = val;
}

/*
 * Gets the Block size from the Header pointer
 */
inline static size_t getSize(void *p) {
	return (getPtrValue(p) & ~7ULL);
}

/*
 * Gets the Allocated bit from the Header Pointer
 */
inline static bool getAlloc(void *p) {
	return ((getPtrValue(p) & 1ULL) == 1ULL);
}

/*
 * Sets the Allocated bit to 1
 */
inline static void setAllocBitToOne(void *p) {
	*(uint64_t*) p = (getPtrValue(p) | 1ULL);
}

/*
 * Sets the Allocated bit to 0
 */
inline static void setAllocBitToZero(void *p) {
	*(uint64_t*) p = (getPtrValue(p) & ~1ULL);
}

/*
 * Returns the Header pointer from corresponding Block Pointer
 */
inline static void* getHeaderPtr(void *bptr) {
	return ((char*) bptr - WSIZE);
}

/*
 * Returns the Header pointer from its footer pointer
 */
inline static void* getHdrPtrFromFtrPtr(void *fptr) {
	return ((char*) fptr - (getSize(fptr) + WSIZE));
}

/*
 * Returns the Footer pointer from corresponding Block Pointer
 */
inline static void* getFooterPtr(void *bptr) {
	return ((char*) bptr + getSize((char*) bptr - WSIZE));
}

/*
 * Returns the Footer pointer from corresponding Header Pointer
 */
inline static unsigned char* getFtrPtrFromHdrPtr(unsigned char *hptr) {
	return (hptr + (getSize(hptr) + WSIZE));
}

/*
 * Returns the prev Block pointer from the current Block pointer
 */
inline static void* getPrevBlockPtr(void *bptr) {
	char *prevBlockFtrPtr = (char*) bptr - 2 * WSIZE;
	return (prevBlockFtrPtr - getSize(prevBlockFtrPtr));
}

/*
 * returns the prev Header pointer from the current Header Pointer
 */
inline static void* getPrevHdrPtrFromHdrPtr(void *hptr) {
	char *prevBlockFtrPtr = (char*) hptr - WSIZE;
	return (prevBlockFtrPtr - (getSize(prevBlockFtrPtr) + WSIZE));
}

/*
 * returns the prev Header pointer from the current Header Pointer
 */
inline static unsigned char* getPrevFtrPtrFromHdrPtr(void *hptr) {
	return ((unsigned char*) hptr - WSIZE);
}

/*
 * Returns the next Block pointer from the current Block pointer
 */
inline static void* getNextBlockPtr(void *bptr) {
	return ((char*) bptr + (getSize(getHeaderPtr(bptr))) + WSIZE);
}

/*
 * returns the next Header pointer from the current Header Pointer
 */
inline static unsigned char* getNextHdrPtrFromHdrPtr(void *hptr) {
	return ((unsigned char*) hptr + (getSize(hptr) + 2 * WSIZE));
}

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
	return ALIGNMENT * ((x + ALIGNMENT - 1) / ALIGNMENT);
}

/*
 * Allocator function to send address for 16 bytes from the
 * Slab and also if memory in Slabs are exhausted, it requests for
 * more slabs.
 */
void* allocate16ByteChunkSlab() {
	unsigned char *blockPtr = freeListHeadPtr16;
	unsigned char* foundBlockPtr = NULL;

	while (blockPtr != NULL && foundBlockPtr == NULL) {
		uint64_t *bitStatusAddr = (uint64_t *) (blockPtr + WSIZE);
		uint64_t bitStatus = *bitStatusAddr;

		if(bitStatus == ~0ULL) {
			blockPtr = *((unsigned char **)blockPtr);
			continue;
		}

		int i = 63;
		for (; i >= 0; i--) {
			if ((bitStatus & 1ULL << i) == 0)
				break;
		}

		bitStatus = bitStatus | (1ULL << i);
		*(uint64_t *) (bitStatusAddr) = bitStatus;
		foundBlockPtr = (blockPtr + (2*(64-i)) * WSIZE);
	}

	if(foundBlockPtr == NULL && blockPtr == NULL) {

		void *newSlab = malloc(2*WSIZE + 128*WSIZE);
		*(unsigned char **)newSlab = freeListHeadPtr16;
		freeListHeadPtr16 = newSlab;
		*(freeListHeadPtr16 + WSIZE) = 0ULL;
		foundBlockPtr = allocate16ByteChunkSlab();
	}

	return foundBlockPtr;
}

/*
 * It frees the 16 byte "ptr" pointer in argument to mark it free in Slab.
 * Also, it releases the Slab into Seg-list if entire Slab gets freed!
 */
bool free16ByteChunkSlab(void *ptr) {
	unsigned char *blockPtr = freeListHeadPtr16;
	bool retFlag = false;
	void *parentAddr = NULL;

	while (blockPtr != NULL) {

		void *blockStartAddr = (blockPtr + 2*WSIZE);
		void *blockEndAddr = (blockPtr + 130*WSIZE);

		if(ptr >= blockStartAddr && ptr <= blockEndAddr) {
			uint64_t *bitStatusAddr = (uint64_t *) (blockPtr + WSIZE);
			uint64_t bitStatus = *bitStatusAddr;
			bitStatus = bitStatus & ~(1ULL << (63 - (ptr - blockStartAddr)/16));
			*(uint64_t *) (bitStatusAddr) = bitStatus;

			retFlag = true;

			if(bitStatus == 0) {
				if(parentAddr == NULL && *((unsigned char **)blockPtr) == NULL) {
					freeListHeadPtr16 = NULL;
				}
				else if(parentAddr == NULL && *((unsigned char **)blockPtr) != NULL) {
					freeListHeadPtr16 = *((unsigned char **)blockPtr);
				}
				else if(parentAddr != NULL && *((unsigned char **)blockPtr) == NULL) {
					*((unsigned char **)parentAddr) = NULL;
				}
				else if(parentAddr != NULL && *((unsigned char **)blockPtr) != NULL) {
					*((unsigned char **)parentAddr) = *((unsigned char **)blockPtr);
				}
				free(blockPtr);
			}
			break;
		}
		parentAddr = blockPtr;
		blockPtr = *((unsigned char **)blockPtr);
	}

	return retFlag;
}

/*
 * It initializes 16-byte block based Slab containing 64 blocks
 * at the time of init of Heap
 */
void init16ByteChunkSlab() {
	freeListHeadPtr16 = malloc(2*WSIZE + 128*WSIZE);

	*(unsigned char**)freeListHeadPtr16 = NULL;
	*(freeListHeadPtr16 + WSIZE) = 0ULL;

}

/*
 * Allocator function to send address for 32 bytes from the
 * Slab and also if memory in Slabs are exhausted, it requests for
 * more slabs.
 */
void* allocate32ByteChunkSlab() {
	unsigned char *blockPtr = freeListHeadPtr32;
	unsigned char* foundBlockPtr = NULL;

	while (blockPtr != NULL && foundBlockPtr == NULL) {
		uint64_t *bitStatusAddr = (uint64_t *) (blockPtr + WSIZE);
		uint64_t bitStatus = *bitStatusAddr;

		if(bitStatus == ~0ULL) {
			blockPtr = *((unsigned char **)blockPtr);
			continue;
		}

		int i = 63;
		for (; i >= 0; i--) {
			if ((bitStatus & 1ULL << i) == 0)
				break;
		}

		bitStatus = bitStatus | (1ULL << i);
		*(uint64_t *) (bitStatusAddr) = bitStatus;
		foundBlockPtr = (blockPtr + 2*WSIZE + (63-i)*4*WSIZE);
	}

	if(foundBlockPtr == NULL && blockPtr == NULL) {

		void *newSlab = malloc(2*WSIZE + 256*WSIZE);
		*(unsigned char **)newSlab = freeListHeadPtr32;
		freeListHeadPtr32 = newSlab;
		*(freeListHeadPtr32 + WSIZE) = 0ULL;
		foundBlockPtr = allocate32ByteChunkSlab();
	}

	return foundBlockPtr;
}

/*
 * It frees the 32 byte "ptr" pointer in argument to mark it free in Slab.
 * Also, it releases the Slab into Seg-list if entire Slab gets freed!
 */
bool free32ByteChunkSlab(void *ptr) {
	unsigned char *blockPtr = freeListHeadPtr32;
	bool retFlag = false;
	void *parentAddr = NULL;

	while (blockPtr != NULL) {

		void *blockStartAddr = (blockPtr + 2*WSIZE);
		void *blockEndAddr = (blockPtr + 258*WSIZE);

		if(ptr >= blockStartAddr && ptr <= blockEndAddr) {
			uint64_t *bitStatusAddr = (uint64_t *) (blockPtr + WSIZE);
			uint64_t bitStatus = *bitStatusAddr;
			bitStatus = bitStatus & ~(1ULL << (63 - (ptr - blockStartAddr)/32));
			*(uint64_t *) (bitStatusAddr) = bitStatus;

			retFlag = true;

			if(bitStatus == 0) {
				if(parentAddr == NULL && *((unsigned char **)blockPtr) == NULL) {
					freeListHeadPtr32 = NULL;
				}
				else if(parentAddr == NULL && *((unsigned char **)blockPtr) != NULL) {
					freeListHeadPtr32 = *((unsigned char **)blockPtr);
				}
				else if(parentAddr != NULL && *((unsigned char **)blockPtr) == NULL) {
					*((unsigned char **)parentAddr) = NULL;
				}
				else if(parentAddr != NULL && *((unsigned char **)blockPtr) != NULL) {
					*((unsigned char **)parentAddr) = *((unsigned char **)blockPtr);
				}
				free(blockPtr);
			}
			break;
		}
		parentAddr = blockPtr;
		blockPtr = *((unsigned char **)blockPtr);
	}
	return retFlag;
}

/*
 * It initializes 32-byte block based Slab containing 64 blocks
 * at the time of init of Heap
 */
void init32ByteChunkSlab() {
	freeListHeadPtr32 = malloc(2*WSIZE + 256*WSIZE);

	*(unsigned char**)freeListHeadPtr32 = NULL;
	*(freeListHeadPtr32 + WSIZE) = 0ULL;

}

/*
 * Initialize Heap: returns false on error, true on success.
 */
bool mm_init(void) {
	// 1 word for alignment Block
	// 2 words for prologue HDR and FTR
	// 1 word for epilogue HDR
	headPtr = (unsigned char*) mem_sbrk(4 * WSIZE);

	//Failure to initialize heap
	if (headPtr == (void*) -1) {
		printf("ERROR! Unable to request memory in init\n");
		return false;
	}

	putPtrValue(headPtr + WSIZE, packSizeAlloc(0, 1)); //Prologue Header
	putPtrValue(headPtr + 2 * WSIZE, packSizeAlloc(0, 1)); // Prologue Footer
	putPtrValue(headPtr + 3 * WSIZE, packSizeAlloc(0, 1)); // Epilogue Header
	headPtr += 3 * WSIZE; // Setting headPtr to Epilogue Header

	// Resetting SegList Pointers
	for (int i = 0; i < 10; i++)
		segList[i] = NULL;

	// Initialize 16/32-byte based Slabs
	init16ByteChunkSlab();
	init32ByteChunkSlab();

	return true;
}

/*
 * Coalesces the free memory block (represented by its Header @param blockHdr) with its neighbours to avoid external fragmentation
 *
 * Accounts for four cases:
 * 		freeBlock ++ currentFreeBlock ++ freeBlock
 * 		freeBlock ++ currentFreeBlock || allocatedBlock
 * 		allocatedBlock || currentFreeBlock ++ freeBlock
 * 		allocatedBlock || currentFreeBlock || allocatedBlock
 */
static void* coalesce(void *blockHdr) {

	if (getAlloc(blockHdr)) {
		printf("%d Error!! colesce on allocated block %p %lu \n", __LINE__, blockHdr, getPtrValue(blockHdr));
		return blockHdr;
	}

	bool isPrevBlockAlloc = getAlloc(getPrevFtrPtrFromHdrPtr(blockHdr));
	bool isNextBlockAlloc = getAlloc(getNextHdrPtrFromHdrPtr(blockHdr));

	void *coaleasedBlockHdr = blockHdr;

	if (isPrevBlockAlloc && isNextBlockAlloc) {
		coaleasedBlockHdr = blockHdr;
	}
	else if (isPrevBlockAlloc && !isNextBlockAlloc) {
		unsigned char *nextBlockHdr = getNextHdrPtrFromHdrPtr(blockHdr);
		uint64_t nextBlockSize = (uint64_t) getSize(nextBlockHdr);
		unsigned char *nextBlockFtr = getFtrPtrFromHdrPtr(nextBlockHdr);

		removeFreeBlock(nextBlockHdr + WSIZE);

		size_t hdrSize = ((uint64_t) getSize(blockHdr)) + nextBlockSize + 2 * WSIZE;

		putPtrValue(blockHdr, packSizeAlloc(hdrSize, 0));
		putPtrValue(nextBlockFtr, packSizeAlloc(hdrSize, 0));

		coaleasedBlockHdr = blockHdr;
	}
	else if (!isPrevBlockAlloc && isNextBlockAlloc) {
		unsigned char *prevBlockFtr = getPrevFtrPtrFromHdrPtr(blockHdr);
		uint64_t prevBlockSize = (uint64_t) getSize(prevBlockFtr);
		unsigned char *prevBlockHdr = getHdrPtrFromFtrPtr(prevBlockFtr);

		unsigned char *blockFtr = getFtrPtrFromHdrPtr(blockHdr);

		removeFreeBlock(prevBlockHdr + WSIZE);

		size_t hdrSize = prevBlockSize + ((uint64_t) getSize(blockHdr)) + 2 * WSIZE;

		putPtrValue(prevBlockHdr, packSizeAlloc(hdrSize, 0));
		putPtrValue(blockFtr, packSizeAlloc(hdrSize, 0));

		coaleasedBlockHdr = prevBlockHdr;
	}
	else {
		unsigned char *prevBlockFtr = getPrevFtrPtrFromHdrPtr(blockHdr);
		uint64_t prevBlockSize = (uint64_t) getSize(prevBlockFtr);
		unsigned char *prevBlockHdr = getHdrPtrFromFtrPtr(prevBlockFtr);

		unsigned char *nextBlockHdr = getNextHdrPtrFromHdrPtr(blockHdr);
		uint64_t nextBlockSize = (uint64_t) getSize(nextBlockHdr);
		unsigned char *nextBlockFtr = getFtrPtrFromHdrPtr(nextBlockHdr);

		removeFreeBlock(prevBlockHdr + WSIZE);
		removeFreeBlock(nextBlockHdr + WSIZE);

		size_t hdrSize = prevBlockSize + ((uint64_t) getSize(blockHdr)) + nextBlockSize + 4 * WSIZE;

		putPtrValue(prevBlockHdr, packSizeAlloc(hdrSize, 0));
		putPtrValue(nextBlockFtr, packSizeAlloc(hdrSize, 0));

		coaleasedBlockHdr = prevBlockHdr;
	}

	// insert into doubly linked list maintained explicitly in free blocks
	insertFreeBlock(coaleasedBlockHdr + WSIZE);

	return coaleasedBlockHdr;
}

/*
 * Extends heap when Segregated list does not have appropriate sized (@param byteLength) free block as per fit policy
 *
 */
static void* extendHeap(size_t byteLength) {

	// Negative case to capture
	if (getPtrValue(headPtr) != 1) {
		printf("%d Error!! extend heap->headptr is not epilogue word %p %lu\n", __LINE__, headPtr, getPtrValue(headPtr));
	}

	// byteLength is already aligned
	void *newBlockPtr = (void*) mem_sbrk(2 * WSIZE + byteLength); // One for Header and one for footer of new block

	// Unable to extendHeap - failure case
	if (newBlockPtr == (void*) -1) {
		printf("%d mem_sbrk returned -1 %p\n", __LINE__, newBlockPtr);
		return NULL;
	}

	putPtrValue(headPtr, packSizeAlloc(byteLength, 0)); 	//New Block Header
	putPtrValue(getFtrPtrFromHdrPtr(headPtr),				//New Block Footer
	packSizeAlloc(byteLength, 0));
	putPtrValue(getNextHdrPtrFromHdrPtr(headPtr),		//New Heap Epilogue word
	packSizeAlloc(0, 1));

	// merging with penultimate block for epilogue Header
	void *freeMem = coalesce(headPtr);

	headPtr += WSIZE + byteLength + WSIZE;

	return freeMem;
}

/*
 *	Contains place and split policy for free blocks found from Segregated lists
 *
 *	Returns adjusted requested block size after placement policy
 */
static unsigned char* placeOrSplitBlock(unsigned char *blockAddr,
		size_t alignedBlockSize) {

	// Place allocated memory with little internal fragmentation
	if (getSize(blockAddr) <= (alignedBlockSize + 6*WSIZE)) {

		removeFreeBlock(blockAddr + WSIZE);

		setAllocBitToOne(blockAddr);
		setAllocBitToOne(getFtrPtrFromHdrPtr(blockAddr));

		return blockAddr;
	} else {
		// Split block at blockAddr
		removeFreeBlock(blockAddr + WSIZE);

		size_t availableBlockSize = getSize(blockAddr) - (alignedBlockSize + 2 * WSIZE);

		// Cut requested block from the larger block found from the segregated list
		putPtrValue(blockAddr, packSizeAlloc(alignedBlockSize, 1));
		putPtrValue(getFtrPtrFromHdrPtr(blockAddr), packSizeAlloc(alignedBlockSize, 1));

		// Split Free Block
		unsigned char *splitFreeBlockHdr = blockAddr + (2 * WSIZE + alignedBlockSize);
		putPtrValue(splitFreeBlockHdr, packSizeAlloc(availableBlockSize, 0));
		putPtrValue(getFtrPtrFromHdrPtr(splitFreeBlockHdr), packSizeAlloc(availableBlockSize, 0));

		// Merge the split free block with neighbour blocks if possible
		coalesce(splitFreeBlockHdr);

		return blockAddr;
	}
}

/*
 * Finds first block in the sized-class segregated list for the aligned user requested
 * size. It traverses linearly from free block to block with the segregated size-classes list
 *
 * returns free block address if block is found
 * 	else returns NULL
 */
static unsigned char* firstFitBlockHeader(size_t size) {
	unsigned char *foundFreeBlock = NULL;

	// retrives Segregated list size class
	int segListIndex = idxSegList(size);

	//If free block not found in the identified size-class seg-list
	// then search in higher sized seg lists one by one
	while (foundFreeBlock == NULL && segListIndex < 10) {

		unsigned char **freeListPtr = &segList[segListIndex];

		if (*freeListPtr == NULL) {
			segListIndex++;
			continue;
		}
		unsigned char *itr = *freeListPtr; // *freeListPtr points to block (and not to header)
		unsigned char *secondWord = *(unsigned char**) (*freeListPtr + WSIZE);

		while (itr != NULL) {
			secondWord = *(unsigned char**) (itr + WSIZE);
			unsigned char *itrHdr = itr - WSIZE;
			size_t itrBlockSize = getSize(itrHdr);

			// searches for the right sized block or bigger block(20byte overhead) to lower
			// small size splinters blocks in the seg lists
			if (itrBlockSize == size || itrBlockSize > (size + 20 * WSIZE)) {
				foundFreeBlock = itrHdr;
				break;
			}
			itr = secondWord;
		}
		segListIndex++;
	}
	return foundFreeBlock;
}

/*
 * malloc: gives user dynamically allocated memory in 16 byte aligned format
 *
 * returns free block pointer if able to,
 * 		else return NULL in case heap is not able to be extended
 */
void* malloc(size_t size) {
	if (size == 0)
		return NULL;

	mm_checkheap(__LINE__);

	// Sends 16-32 bytes requests to Slab allocator
	if(size <= 16)
		return allocate16ByteChunkSlab();
	if(size > 16 && size<=32)
		return allocate32ByteChunkSlab();

	// aligns to 16 byte blocks
	size_t alignedBlockSize = align(size);

	unsigned char *firstFitBlockHdrAddr = firstFitBlockHeader(alignedBlockSize);

	// If a suitable size free block found from first-fit policy
	if (firstFitBlockHdrAddr) {

		unsigned char *allocatedBlockHdr = placeOrSplitBlock(firstFitBlockHdrAddr, alignedBlockSize);
		return allocatedBlockHdr + WSIZE;
	}
	else {
		// Otherwise Extend Heap by calling mem_sbrk
		void *newBlockAddr = extendHeap(alignedBlockSize);

		if (newBlockAddr) {
			unsigned char *allocatedBlockHdr = placeOrSplitBlock(newBlockAddr, alignedBlockSize);
			return (allocatedBlockHdr + WSIZE);
		}
		else
			return NULL;
	}
	return NULL;
}

/*
 * free: frees dynamically allocated pointer which was given to user earlier via malloc/realloc
 *
 * It frees the memory and then coaleses the free block with neighbouring free blocks
 */
void free(void *ptr) {
	if (ptr == NULL)
		return;

	// Free, if ptr belongs to 16 byte based Slabs
	if(free16ByteChunkSlab(ptr))
		return;

	// Free, if ptr belongs to 32 byte based Slabs
	if(free32ByteChunkSlab(ptr))
		return;

	// sets the allocation flag bit to 0 in the Header Block
	putPtrValue(getHeaderPtr(ptr), packSizeAlloc(getSize(ptr - WSIZE), 0)); // Set alloc bit to 0 in Header
	putPtrValue(getFooterPtr(ptr), packSizeAlloc(getSize(ptr - WSIZE), 0)); // Set alloc bit to 0 in Footer

	// merge with neighbouring free blocks
	coalesce(getHeaderPtr(ptr));

	mm_checkheap(__LINE__);

	return;
}

/*
 * Splits the block for realloc function in case of size-reduction is called on a allocated block
 * It also calls coalesce upon freed blocks
 */
static unsigned char* splitBlock(unsigned char *blockAddr, size_t alignedBlockSize) {
	// Split the fitBlock Addr
	size_t firstFitBlockSize = getSize(blockAddr);
	size_t availableBlockSize = firstFitBlockSize - (alignedBlockSize + 2 * WSIZE);

	// Requested Block
	putPtrValue(blockAddr, packSizeAlloc(alignedBlockSize, 1));
	putPtrValue((blockAddr + (WSIZE + alignedBlockSize)), packSizeAlloc(alignedBlockSize, 1));

	// Free Block
	unsigned char *splitFreePtr = blockAddr + 2 * WSIZE + alignedBlockSize;
	putPtrValue(splitFreePtr, packSizeAlloc(availableBlockSize, 0));
	putPtrValue(splitFreePtr + (WSIZE + availableBlockSize), packSizeAlloc(availableBlockSize, 0));

	coalesce(splitFreePtr);

	return blockAddr;
}

/*
 * realloc: Re-adjusts the memory sizes for the allocated block for the user
 * (made inefficient due to Slab allocator logic)
 */
void* realloc(void *oldptr, size_t size) {
	// Free the pointer if size is zero
	if (size == 0) {
		free(oldptr);
		return NULL;
	}

	if (oldptr == NULL)
		return malloc(size);
//	else {
//		size_t currentBlockSize = getSize(getHeaderPtr(oldptr));
		size_t alignedBlockSize = align(size);
//
//		// Comparison to allocate a new memory block or not
//		if (currentBlockSize == alignedBlockSize)
//			return oldptr;
//		else if (currentBlockSize == (alignedBlockSize + 2 * WSIZE))
//			return oldptr;
//		else if (currentBlockSize > alignedBlockSize) {
//			void *oldPtrHdr = getHeaderPtr(oldptr);
//			unsigned char *allocatedBlockHdr = splitBlock(oldPtrHdr, alignedBlockSize);
//			return (allocatedBlockHdr + WSIZE);
//		}
//		else {
			//Get addr of new memory for atleast size bytes
			void *newptr = malloc(alignedBlockSize);
			memcpy(newptr, oldptr, alignedBlockSize); // Copies the data from old to new block
			free(oldptr);
			return newptr;
//		}
//	}
//	return NULL;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

// Doubly Linked list operation functions which are placed explicitly within free blocks

// Two 8 byte words are maintained within free block:
//		prevAddr represents previous block address
//		nextAddr represents next block address
inline static unsigned char* getFreeBlockPrevAddr(unsigned char *ptr) {
	return *(unsigned char**) ptr;
}
inline static void writePrevSection(void *ptr, void *data) {
	*(unsigned char**) ((unsigned char*) ptr) = data;
}
inline static unsigned char* getFreeBlockNextAddr(unsigned char *ptr) {
	return *(unsigned char**) (ptr + WSIZE);
}
inline static void writeNextSection(void *ptr, void *data) {
	*(unsigned char**) ((unsigned char*) ptr + WSIZE) = data;
}

// Inserts a block in right sized segregated-list and readjusts pointers within the list
// works on LIFO order
static void insertFreeBlock(void *ptr) {

	if (getAlloc(getHeaderPtr(ptr))) {
		printf("Error!! Allocated block to be inserted into free list");
		return;
	}
	size_t ptrBlockLength = getSize(getHeaderPtr(ptr));
	unsigned char **freeListPtr = &segList[idxSegList(ptrBlockLength)];

	if (*freeListPtr == ptr)
		return;

	if (*freeListPtr == NULL) {
		writePrevSection(ptr, NULL);
		writeNextSection(ptr, NULL);
	} else {
		writePrevSection(ptr, NULL);
		writeNextSection(ptr, *freeListPtr);
		*(unsigned char**) (*freeListPtr) = ptr;
	}
	*freeListPtr = ptr;
}

// Removes a free block from seg-list in case of malloc/realloc call
// from appropriate size-class seg list and readjusts the doubly linked list pointers
static void removeFreeBlock(void *ptr) {
	size_t ptrBlockLength = getSize(getHeaderPtr(ptr));
	unsigned char **freeListPtr = &segList[idxSegList(ptrBlockLength)];

	if (*freeListPtr == NULL)
		return;

	unsigned char *prevSection = *(unsigned char**) ((unsigned char*) ptr);
	unsigned char *nextSection = *(unsigned char**) ((unsigned char*) ptr + WSIZE);

	if (prevSection == NULL && nextSection == NULL) {
		*freeListPtr = NULL;
	}
	else if (prevSection == NULL && nextSection != NULL) {
		*freeListPtr = nextSection;
		writePrevSection(*freeListPtr, NULL);
	}
	else if (prevSection != NULL && nextSection == NULL) {
		writeNextSection(prevSection, NULL);
	}
	else if (prevSection != NULL && nextSection != NULL) {
		writePrevSection(nextSection, prevSection);
		writeNextSection(prevSection, nextSection);
	}
}

// returns id of the free list within seg-lists array based on the @param blockLength
static int idxSegList(size_t blockLength) {
	if (blockLength <= 64)
		return 0;
	if (blockLength > 64 && blockLength <= 128)
		return 1;
	if (blockLength > 128 && blockLength <= 256)
		return 2;
	if (blockLength > 256 && blockLength <= 512)
		return 3;
	if (blockLength > 512 && blockLength <= 1024)
		return 4;
	if (blockLength > 1024 && blockLength <= 2048)
		return 5;
	if (blockLength > 2048 && blockLength <= 4096)
		return 6;
	if (blockLength > 4096 && blockLength <= 8192)
		return 7;
	if (blockLength > 8192 && blockLength <= 16384)
		return 8;
	else
		return 9;
}

//Debug functions
static void printBlockOnHeap(void* ptr) {
	int i = 1;
	unsigned char *itr = mem_heap_lo() + 1 * WSIZE;
	unsigned char *prev = itr;
	while (itr <= (unsigned char*) (mem_heap_hi() + 1)) {
		unsigned char *blockAddr = itr + WSIZE;
		if((unsigned char*)ptr <= itr) {
			printf("PrevHeader%d -> Addr=%p Size=%ld AllocBit=%d\n", i, prev, getSize(prev), getAlloc(prev));
			printf("Header%d -> Addr=%p Size=%ld AllocBit=%d\n", i, itr, getSize(itr), getAlloc(itr));
			printf("Block%d -> Addr=%p sizeof=%ld\n", i, blockAddr, sizeof(blockAddr));
			unsigned char *ftr = itr + getSize(itr) + WSIZE;
			printf("Footer%d -> Addr=%p Size=%ld AllocBit=%d\n\n", i, ftr, getSize(ftr), getAlloc(ftr));
			break;
		}
		i++;
		prev = itr;
		itr += getSize(itr) + 2 * WSIZE;
	}
}

static void printHeap() {
	int i = 1;
	unsigned char *itr = mem_heap_lo() + 1 * WSIZE;

	printf("Heap_low addr: %p\n", mem_heap_lo());
	printf("Heap_hi addr: %p\n", mem_heap_hi());

	while (itr <= (unsigned char*) (mem_heap_hi() + 1)) {
		printf("Header%d -> Addr=%p Size=%ld AllocBit=%d\n", i, itr, getSize(itr), getAlloc(itr));
		unsigned char *blockAddr = itr + WSIZE;
		printf("Block%d -> Addr=%p sizeof=%ld\n", i, blockAddr, sizeof(blockAddr));
		unsigned char *ftr = itr + getSize(itr) + WSIZE;
		printf("Footer%d -> Addr=%p Size=%ld AllocBit=%d\n\n", i, ftr, getSize(ftr), getAlloc(ftr));
		i++;
		itr += getSize(itr) + 2 * WSIZE;
	}
}

static void searchHeapForEmptyBlocks(size_t size) {
	unsigned char *itr = mem_heap_lo() + 1 * WSIZE;
	int count = 0, fragmentedMem = 0;
	bool flag = false;

	while (itr <= (unsigned char*) (mem_heap_hi() + 1)) {

		if (!getAlloc(itr)) {
			count++;
			fragmentedMem += getSize(itr);
			if (getSize(itr) > size)
				flag = true;

		}

		itr += getSize(itr) + 2 * WSIZE;
	}
	if (count >= 1 || flag || fragmentedMem > 0)
		printf("WARNING! Fragmented memory! Size=%d Blocks=%d Flag=%d", fragmentedMem, count, flag);
}

static void printOneWord(unsigned char *ptr) {
	unsigned char *firstWord = *(unsigned char**) (ptr);
	unsigned char *secondWord = *(unsigned char**) (ptr + WSIZE);
	printf("%p=[%p :: %p] ", ptr, firstWord, secondWord);

	printf("\n");
}

static void traverse(unsigned char *freeListPtr) {
	if (freeListPtr == NULL) {
		printf("traverse:: freeListPtr NULL\n");
		return;
	}

	unsigned char *itr = freeListPtr;

	unsigned char *firstWord = *(unsigned char**) (freeListPtr);
	unsigned char *secondWord = *(unsigned char**) (freeListPtr + WSIZE);

	while (itr != NULL) {
		firstWord = *(unsigned char**) (itr);
		secondWord = *(unsigned char**) (itr + WSIZE);
		printf("%p (%ld)=[%p :: %p]\n", itr, getSize(itr - WSIZE), firstWord,
				secondWord);
		itr = secondWord;
		if (firstWord != NULL && firstWord == secondWord)
			break;
	}
}

static void traverseAllSegList() {
	printf("Seglist [0]: \n");	traverse(segList[0]);
	printf("Seglist [1]: \n");	traverse(segList[1]);
	printf("Seglist [2]: \n");	traverse(segList[2]);
	printf("Seglist [3]: \n");	traverse(segList[3]);
	printf("Seglist [4]: \n");	traverse(segList[4]);
	printf("Seglist [5]: \n");	traverse(segList[5]);
	printf("Seglist [6]: \n");	traverse(segList[6]);
	printf("Seglist [7]: \n");	traverse(segList[7]);
	printf("Seglist [8]: \n");	traverse(segList[8]);
	printf("Seglist [9]: \n");	traverse(segList[9]);
	printf("Seglist [10]: \n");	traverse(segList[10]);
	printf("Seglist [11]: \n");	traverse(segList[11]);
}
static void print16BHeap() {
	unsigned char *blockPtr = freeListHeadPtr16;
	static int i=1;
	printf("PRINTING 16B HEAP\n");
	while (blockPtr != NULL) {
		printf("ADDR%d = %p\n", i, blockPtr);
		blockPtr = *((unsigned char **)blockPtr);
	}
}

static bool isPtrInside16BHeap(void *ptr) {
	unsigned char *blockPtr = freeListHeadPtr16;

	while (blockPtr != NULL) {
		void *blockStartAddr = ((unsigned char*) blockPtr + 2 * WSIZE);
		void *blockEndAddr = ((unsigned char*) blockPtr + 130 * WSIZE);

		if (ptr >= blockStartAddr && ptr <= blockEndAddr) {
			return true;
		}

		blockPtr = *((unsigned char**) blockPtr);
	}
	return false;
}


/*
 * Heap Checker Functions to check invariants
 */

//	Checks if there are more than two Slabs empty for 16 byte / 32 byte
void areMultipleSlabsFree(int lineno) {
	unsigned char *blockPtr16 = freeListHeadPtr16;

	int cnt16B = 0;
	while (blockPtr16 != NULL) {
		uint64_t *bitStatusAddr = (uint64_t *) (blockPtr16 + WSIZE);
		uint64_t bitStatus = *bitStatusAddr;

		if(bitStatus == ~0ULL)
			continue;

		cnt16B ++;

		if(cnt16B >= 2) {
			printf("ERROR! Line:%d Multiple 16 bytes block slabs are free! \n", lineno);
		}
		blockPtr16 = *((unsigned char **)blockPtr16);
	}

	unsigned char *blockPtr32 = freeListHeadPtr32;

	int cnt32B = 0;
	while (blockPtr32 != NULL) {
		uint64_t *bitStatusAddr = (uint64_t *) (blockPtr32 + WSIZE);
		uint64_t bitStatus = *bitStatusAddr;

		if(bitStatus == ~0ULL)
			continue;

		cnt32B ++;

		if(cnt32B >= 2) {
			printf("ERROR! Line:%d Multiple 32 bytes block slabs are free! \n", lineno);
		}
		blockPtr32 = *((unsigned char **)blockPtr32);
	}

}

//	Checks if all free blocks in Segregated lists are marked free and belong to right size-class in Segregated list
void checkFreeBlockSizeAndAllocBitInSegLists(int lineno) {

	for (int i = 0; i < 10; i++) {
		unsigned char *itr = segList[i];

		if (itr == NULL)
			continue;

		while (itr != NULL) {

			if(getAlloc(getHeaderPtr(itr))) {
				printf("ERROR! Line:%d Allocated Block(%p) Found in SegList[%d]\n", lineno, itr, i);
			}
			if(!(idxSegList(getSize(getHeaderPtr(itr))) == i)) {
				printf("ERROR! Line:%d Allocated Block(%p) sized(%ld) found in wrong SegList[%d]\n", lineno, itr, getSize(getHeaderPtr(itr)), i);
			}

			itr = *(unsigned char**) (itr + WSIZE);
		}
	}
}

// Checks if bp (block pointer) is present in right size-class Segregated List
bool isPresentInSegList(unsigned char *bp) {
	bool isPresentFlag = false;
	int segListIndex = idxSegList(getSize(getHeaderPtr(bp)));

	unsigned char *itr = segList[segListIndex];
	unsigned char *secondWord = *(unsigned char**) (segList[segListIndex] + WSIZE);

	while (itr != NULL) {
		secondWord = *(unsigned char**) (itr + WSIZE);

		if (itr == bp) {
			isPresentFlag = true;
			break;
		}
		itr = secondWord;
	}
	return isPresentFlag;
}

//	Traverses heap and checks for some invariants
void traverseHeapCheckInvariants(int lineno) {
	unsigned char *itr = mem_heap_lo() + 3*WSIZE;

	while (itr <= (unsigned char*) (mem_heap_hi() + 1)) {

		//Checks if Size differs in Header and Footer in a Block
		if(!(itr == headPtr) && (getSize(itr) != getSize(getFtrPtrFromHdrPtr(itr)))) {
			printf("ERROR! Line:%d Block Size mismatch in Header(%p)(%ld) and Footer(%p)(%ld)\n", lineno, itr, getSize(itr), getFtrPtrFromHdrPtr(itr), getSize(getFtrPtrFromHdrPtr(itr)));
		}

		//Checks if AllocationBit differs in Header and Footer in a Block
		if(!(itr == headPtr) && (getAlloc(itr) != getAlloc(getFtrPtrFromHdrPtr(itr)))) {
			printf("ERROR! Line:%d AllocationBit mismatch in Header(%p)(%d) and Footer(%p)(%d)\n", lineno, itr, getAlloc(itr), getFtrPtrFromHdrPtr(itr), getAlloc(getFtrPtrFromHdrPtr(itr)));
		}

		//Check if there are any contiguous free blocks that somehow escaped coalescing
		if(!(itr == headPtr) && !getAlloc(itr) && !getAlloc(getNextHdrPtrFromHdrPtr(itr))) {
			printf("ERROR! Line:%d Contiguous free blocks found! HdrPtr1 (%p) - HdrPtr2 (%p)\n", lineno, itr, getNextHdrPtrFromHdrPtr(itr));
		}

		// Check if all free blocks in Heap are there in Segregated list
		if(!getAlloc(itr) && !isPresentInSegList(itr + WSIZE)) {
			printf("ERROR! Line:%d Free block in Heap but not found in SegList! HdrPtr1 (%p) - BlkPtr2 (%p)\n", lineno, itr, (itr + WSIZE));
		}

		itr += getSize(itr) + 2 * WSIZE;
	}
}

//Checks if circular loop is encountered while traversing linked list
void checkCycleInLinkedList(int lineno) {
	// Check for 16 byte Slabs
	unsigned char *blockPtr16 = freeListHeadPtr16;

	if((unsigned char **)freeListHeadPtr16 != NULL) {
		unsigned char *fastBlockPtr16 = *((unsigned char **)freeListHeadPtr16);

		while (blockPtr16 != NULL && fastBlockPtr16 != NULL) {

			if(blockPtr16 == fastBlockPtr16)
				printf("ERROR! Line:%d Cycle detected in 16 bytes slabs linked list! \n", lineno);

			blockPtr16 = *((unsigned char **)blockPtr16);
			fastBlockPtr16 = *((unsigned char **)blockPtr16);
		}
	}


	// Check for 32 byte Slabs
	unsigned char *blockPtr32 = freeListHeadPtr32;

	if((unsigned char **)freeListHeadPtr32 != NULL) {
		unsigned char *fastBlockPtr32 = *((unsigned char **)freeListHeadPtr32);

		while (blockPtr32 != NULL && fastBlockPtr32 != NULL) {

			if(blockPtr32 == fastBlockPtr32)
				printf("ERROR! Line:%d Cycle detected in 32 bytes slabs linked list! \n", lineno);

			blockPtr32 = *((unsigned char **)blockPtr32);
			fastBlockPtr32 = *((unsigned char **)blockPtr32);
		}
	}

}
/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG

//	Checks if circular loop is encountered while traversing linked list
	checkCycleInLinkedList(lineno);

//	Checks if there are more than two Slabs empty for 16 bytes / 32 bytes
	areMultipleSlabsFree(lineno);

//	Traverses heap and checks for some invariants
	traverseHeapCheckInvariants(lineno);

//	Check if all free blocks in Segregated lists are marked free and belong to right size-class
	checkFreeBlockSizeAndAllocBitInSegLists(lineno);

#endif /* DEBUG */
    return true;
}
