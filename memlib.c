/*
 * memlib.c - a module that simulates the memory system.  Needed because it 
 *            allows us to interleave calls from the student's malloc package 
 *            with the system's malloc package in libc.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#include <errno.h>

#include "memlib.h"
#include "config.h"

/* private variables */
static char *mem_start_brk;  /* points to first byte of heap */
static char *mem_brk;        /* points to last byte of heap */
static char *mem_max_addr;   /* largest legal heap address */ 
// 개인적인 생각이지만 굳이 내가 현재 가용가능한 힙의 영역의 맥시멈과 실제 힙의 맥시멈을 따로 관리해주는건
// 가상메모리의 개념과 유사한 것 같음. 전체 힙 영역에서 가용 가능한 특정 범위를 부여함으로써 전체 힙을 단독으로 사용하는 것 처럼 해주는..?? 
/* 
 * mem_init - initialize the memory system model
 */
void mem_init(void)
{
    /* allocate the storage we will use to model the available VM */
    if ((mem_start_brk = (char *)malloc(MAX_HEAP)) == NULL) { // max_heap = 20MB
	fprintf(stderr, "mem_init_vm: malloc error\n");
	exit(1);
    }

    mem_max_addr = mem_start_brk + MAX_HEAP;  /* max legal heap address */
    mem_brk = mem_start_brk;                  /* heap is empty initially */
    // 초기 힙은 비어있으므로 heap의 첫번째 및 마지막 바이트를 가리키는 변수가 동일함.
}

/* 
 * mem_deinit - free the storage used by the memory system model
 */
void mem_deinit(void)
{
    free(mem_start_brk);
}

/*
 * mem_reset_brk - reset the simulated brk pointer to make an empty heap
 */
void mem_reset_brk()
{
    mem_brk = mem_start_brk;
}

/* 
 * mem_sbrk - simple model of the sbrk function. Extends the heap 
 *    by incr bytes and returns the start address of the new area. In
 *    this model, the heap cannot be shrunk.
 */

// 가용할 수 있는 힙의 영역을 확장해주고(mem_brk += incr), 확장하기전 위치를 반환
// incr 만큼 확장시키고 mem_brk를 크기만큼 더해줘서 이만큼까지 사용할 수 있다 갱신해주는 것
// 확장하는 영역이 heap_max를 초과하는지 확인해줌.

void *mem_sbrk(int incr) 
{
    char *old_brk = mem_brk; /* points to first byte of heap */

    if ( (incr < 0) || ((mem_brk + incr) > mem_max_addr)) { /* largest legal heap address */ 
	errno = ENOMEM;
	fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory...\n");
	return (void *)-1;
    }
    mem_brk += incr;
    return (void *)old_brk; // 확장하기 전 위치
}

/*
 * mem_heap_lo - return address of the first heap byte
 */
void *mem_heap_lo()
{
    return (void *)mem_start_brk;
}

/* 
 * mem_heap_hi - return address of last heap byte
 */
void *mem_heap_hi()
{
    return (void *)(mem_brk - 1);
}

/*
 * mem_heapsize() - returns the heap size in bytes
 */
size_t mem_heapsize() 
{
    return (size_t)(mem_brk - mem_start_brk);
}

/*
 * mem_pagesize() - returns the page size of the system
 */
size_t mem_pagesize()
{
    return (size_t)getpagesize();
}
