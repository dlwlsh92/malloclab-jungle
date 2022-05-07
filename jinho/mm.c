/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 // Word and header/footer size (bytes)
#define DSIZE 8 // Double word size (bytes)
#define CHUNKSIZE (1<<12) // Extend heap by this amount (bytes)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// Read the size and allocated fields from address p
// 0x7이 111이므로 not을 통해 할당에 관련된 비트 3자리를 제외한 모든 자리를 1로 만들어 비트 연산을 이용해 블록 사이즈를 얻음
#define GET_SIZE(p) (GET(p) & ~0x7)
// 비트 연산을 통해 가용 블록인지 아닌지 반환함. 가용이면 0, else 1
#define GET_ALLOC(p) (GET(p) & 0x1)

// Given bloack ptr bp, compute address of its header and footer
// bp는 payload가 시작하는 위치를 가리킴
#define HDRP(bp) ((char *)(bp) - WSIZE) // 현재 블록의 헤더 위치
// 현재 bp에서 현재 블록의 크기만큼을 더하면 다음 블록의 bp가 되기 때문에 여기서 2word를 빼면 현재 블록의 풋터 위치가 됨.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 현재 bp에서 1word를 빼면 현재 블록의 헤더를 가리키고, 현재 bp에서 현재 블록의 크기만큼 더해주면 다음 블록의 bp 위치가 됨.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 현재 bp에서 2word를 빼면 이전 블록의 풋터를 가리키고, 현재 bp에서 이전 블록의 크기만큼 빼주면 이전 블록의 bp 위치가 됨
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void *heap_listp; // find fit에서 사용하기 위한 정적 전역 변수이다.
static void *coalesce(void *); 
static void *find_fit(size_t);
static void place(void *, size_t);

/* 
 * mm_init - initialize the malloc package.
 */

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // words가 홀수면 1을 더해서 4를 곱하고, 짝수면 그대로 4를 곱함.
    // 짝수에다가 4를 곱하면 무조건 8의 배수
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 최소 블록의 단위인 8바이트를 맞춰주기 위함
    // sbrk에서 확장하고자 하는 범위가 max_heap을 초과할 경우 -1을 리턴
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    // 현재 가용 가능한 힙의 마지막 point(old_brk = mem_brk(확장 전))를 리턴하기 때문에
    // 해당 위치의 헤더 및 풋터에 확장시킨 크기와 가용 상태를 pack 해주고
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // 확장한 영역 뒤에 에필로그 헤더 생성 및 (0, 1) pack

    return coalesce(bp); // 확장하기 전 블록이 가용 블록일 경우 확장한 블록과 합쳐주기 위함.
}




int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // 프롤로그 및 에필로그 블록 생성을 위한 힙 영역 확장
        return -1;
    PUT(heap_listp, 0); // 힙이 첫번째 블록에 0 삽입
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록의 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록의 풋터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // 에필로그 블록의 헤더
    heap_listp += (2*WSIZE); // 프롤로그 블록의 풋터를 가리킴

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){ // 힙 영역 확장의 최소 단위인 CHUNKSIZE(2^12bytes=4096bytes) 크기만큼 확장
        return -1; // max_heap 초과하면 -1 리턴
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize; // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit
    char *bp;

    if (size==0) return NULL;

    if (size <= DSIZE){ // size가 8bytes보다 같거나 작을 경우 헤더, 풋터를 포함하여 필요한 최소 크기인 16bytes를 할당
        asize = 2*DSIZE;
    }
    else {
        // size를 포함할 수 있는 8바이트로 정렬된 최소 데이터 크기를 계산하기 위함. 꼭 -1이어야 불필요한 크기를 할당 받는 경우가 없음.
        // 다음에 볼 때 쯤이면 잊어버리고 왜?? 할 수도 있으니 직접!! 그림을 그려볼 것^^
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 
    }

    if ((bp = find_fit(asize)) != NULL){ // 가용 블록을 찾기 위한 과정, first_fit임
        place(bp, asize); // 헤더와 풋터를 설정해주고, 메모리 누수를 방지하기 위해 블록을 분리시킴
        // (넣어줄 가용 블록 크기 - 할당한 크기)만큼을 가용공간으로 할당해줌
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE); // 가용 블록이 없을 경우, 힙의 영역을 확장시켜주기 위한 데이터 크기
    // 확장을 위한 기본 크기인 CHUNKSIZE와 필요한 블록 크기를 비교해서 더 큰 값으로 사용
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;

    place(bp, asize);
    return bp;

}

/*
 * mm_free - Freeing a block does nothing.
 */
// free는 블록을 가용상태로 만들어주는 것 뿐이지 데이터 자체의 값을 초기화 해주는 것이 아님(이전 데이터들이 그대로 들어있음.)
// calloc은 할당 할 때, 데이터 값을 0으로 초기화 해줌
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    // 현재 블록의 헤더와 풋터에 현재 블록 크기와 가용 상태를 pack 해줌
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp); // 할당 해제 시 해당 블록의 앞, 뒤 블록의 가용 여부를 확인해서 합쳐줌.
}

static void *coalesce(void *bp){
    // 현재 블록의 이전 및 다음 블록의 가용 여부 확인(0 or 1)
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if (prev_alloc && next_alloc){ // 이전 블록 및 다음 블록이 할당된 상태면 합칠 블록이 없으므로 현재 위치를 리턴
        return bp;
    }

    else if (prev_alloc && !next_alloc){ // 다음 블록만 가용 가능한 상태인 경우
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록 크기에 다음 블록의 사이즈를 더해줌
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록의 헤더에 갱신된 블록 크기와 가용 가능 여부를 갱신해줌
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록의 풋터에 헤더와 동일하게 갱신해줌
    }

    else if (!prev_alloc && next_alloc){ // 이전 블록만 가용 가능한 상태인 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록 크기 더해줌
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 풋터 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더 갱신
        bp = PREV_BLKP(bp); // bp는 이전 블록의 bp로 갱신
    }

    else{ // 현재 블록의 전, 후 블록 모두 가용 가능한 상태인 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        // 이전 블록 및 다음 블록의 크기를 더해줌
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 풋터 갱신
        bp = PREV_BLKP(bp); // 이전 블록의 bp로 갱신
    }

    return bp;
}

static void *find_fit(size_t asize){

    void *bp;
    // heap_listp부터 epilogue block까지 확인(에필로그 블록의 사이즈가 0이기 때문에 조건에 걸림)
    // bp는 다음 블록의 bp로 계속 갱신함
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            // 해당 블록이 가용 상태이고, 블록 크기가 asize보다 같거나 큰 경우
            return bp; // 해당 블록의 bp 리턴
        }
    }
    return NULL; // 못찾으면 NULL 값 리턴
}

static void place(void *bp, size_t asize){ // 할당할 블록의 bp 및 ***필요한 블록의 크기
    size_t csize = GET_SIZE(HDRP(bp)); // 할당할 블록의 크기

    // (할당할 블록의 크기 - 필요한 블록의 크기)가 16바이트보다 같거나 클 경우 내부 단편화를 줄이기 위해
    // 최소 필요 블록 크기인 16바이트를 기준으로 분리시킴
    if ((csize - asize) >= (2*DSIZE)) {  
        PUT(HDRP(bp), PACK(asize, 1)); // 헤더의 블록 사이즈를 csize에서 asize로 갱신
        PUT(FTRP(bp), PACK(asize, 1)); // 헤더와 동일(앞에서 헤더의 크기가 바뀌었기 때문에 풋터의 위치는 asize로 갱신된 크기를 반영한 위치임)
        bp = NEXT_BLKP(bp); // 남는 부분을 가용 블록으로 만들어주기 위함
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 가용 블록으로 사용하기 위해 사이즈 갱신
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else { // 16바이트보다 작을 경우 할당할 블록의 크기 그대로 반영
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//       return NULL;
//     copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     if (size < copySize)
//       copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }

void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0) // 변경할 크기가 0일 경우, free와 동일한 기능 수행
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL) // bp가 NULL일 경우, malloc과 동일한 기능 수행
    {
        return mm_malloc(size);
    }

    void *newp = mm_malloc(size);
    if (newp == NULL) // 메모리 크기가 max_heap 크기를 초과했을 때
    {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp)); 
    if (size < oldsize) 
    {
        oldsize = size;
    }
    memcpy(newp, bp, oldsize); // 메모리 값을 복사함. 
    //(복사받은 메모리를 가리키는 포인터, 복사할 메모리를 가리키는 포인터, 복사할 데이터의 길이(byte))
    mm_free(bp); // 이전 블록 할당 해제
    return newp; // 새로운 블록의 bp 리턴
}














