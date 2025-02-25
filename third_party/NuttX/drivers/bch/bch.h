/****************************************************************************
 * drivers/bch/bch.h
 *
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.  The
 * ASF licenses this file to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
 * License for the specific language governing permissions and limitations
 * under the License.
 *
 ****************************************************************************/

#ifndef __DRIVERS_BCH_BCH_H
#define __DRIVERS_BCH_BCH_H

/****************************************************************************
 * Included Files
 ****************************************************************************/

#include <sys/types.h>
#include <stdint.h>
#include <stdbool.h>
#include <semaphore.h>
#include "fs/fs.h"
#include "disk.h"
#include "user_copy.h"

/****************************************************************************
 * Pre-processor Definitions
 ****************************************************************************/

#define bchlib_semgive(d) (void)sem_post(&(d)->sem)  /* To match bchlib_semtake */
#define MAX_OPENCNT       (255)                      /* Limit of uint8_t */
#define DIOC_GETPRIV      (0x1000)

/****************************************************************************
 * Public Types
 ****************************************************************************/

struct bchlib_s
{
  struct Vnode *vnode;           /* I-node of the block driver */
  uint32_t sectsize;             /* The size of one sector on the device */
  unsigned long long nsectors;   /* Number of sectors supported by the device */
  unsigned long long sector;     /* The current sector in the buffer */
  sem_t sem;                     /* For atomic accesses to this structure */
  uint8_t refs;                  /* Number of references */
  bool dirty;                    /* true: Data has been written to the buffer */
  bool readonly;                 /* true: Only read operations are supported */
  bool unlinked;                 /* true: The driver has been unlinked */
  uint8_t *buffer;               /* One sector buffer */
  los_disk *disk;
  unsigned long long sectstart;
};

/****************************************************************************
 * Public Data
 ****************************************************************************/

#undef EXTERN
#if defined(__cplusplus)
#define EXTERN extern "C"
extern "C" {
#else
#define EXTERN extern
#endif

EXTERN const struct file_operations_vfs bch_fops;

/****************************************************************************
 * Public Function Prototypes
 ****************************************************************************/

EXTERN void bchlib_semtake(struct bchlib_s *bch);
EXTERN int  bchlib_flushsector(struct bchlib_s *bch);
EXTERN int  bchlib_readsector(struct bchlib_s *bch, unsigned long long sector);
EXTERN int bchlib_setup(const char *blkdev, bool readonly, void **handle);
EXTERN int bchlib_teardown(void *handle);
EXTERN ssize_t bchlib_read(void *handle, char *buffer, loff_t offset, size_t len);
EXTERN ssize_t bchlib_write(void *handle, const char *buffer, loff_t offset, size_t len);

#undef EXTERN
#if defined(__cplusplus)
}
#endif

#endif /* __DRIVERS_BCH_BCH_H */
