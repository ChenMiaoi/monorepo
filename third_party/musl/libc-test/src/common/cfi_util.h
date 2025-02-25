/**
 * Copyright (c) 2023 Huawei Device Co., Ltd.
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdio.h>
#include <string.h>
#include <dirent.h>
extern "C" {
    #include "test.h"
}

#define UBSAN_LOG_DIR "/data/log/sanitizer/ubsan/"
#define UBSAN_LOG_TAG "ubsan"
#define DEBUG 0
#define BUFFER_SIZE 4096

static void ShowCfiLogFile()
{
    DIR *dir;
    struct dirent *ptr;
    dir = opendir(UBSAN_LOG_DIR);
    while ((ptr = readdir(dir)) != NULL) {
        if (strstr(ptr->d_name, UBSAN_LOG_TAG) != NULL) {
            printf("%s: %s\n", UBSAN_LOG_DIR, ptr->d_name);
        }
    }
    closedir(dir);
}

static void ClearCfiLog()
{
    DIR *dir;
    struct dirent *ptr;
    dir = opendir(UBSAN_LOG_DIR);
    while ((ptr = readdir(dir)) != NULL) {
        if (strstr(ptr->d_name, UBSAN_LOG_TAG) != NULL) {
            char tmp[BUFFER_SIZE] = UBSAN_LOG_DIR;
            strcat(tmp, ptr->d_name);
            remove(tmp);
        }
    }
    closedir(dir);
}

static void CheckCfiLog(char *file, const char *needle)
{
    if (DEBUG) {
        printf("[cfi checking]:%s\n", file);
    }
    char buffer[BUFFER_SIZE];
    FILE *fp = fopen(file, "r");
    if (!fp) {
        return;
    }
    if (fseek(fp, 0, SEEK_END) == -1) {
        return;
    }
    int size = ftell(fp);
    if (size <= 0) {
        fclose(fp);
        t_error("FAIL %s size is <=0!\n", file);
    }
    if (fseek(fp, 0, SEEK_SET) == -1) {
        fclose(fp);
        return;
    }
    int rsize = fread(buffer, 1, size, fp);
    if (rsize == 0) {
        fclose(fp);
        return;
    }

    if (strstr(buffer, needle) != NULL) {
        printf("[cfi checking] %s is ok.\n", needle);
    } else {
        t_error("FAIL %s is failed!\n", needle);
    }
    fclose(fp);
}

static void FindAndCheck(const char *pattern)
{
    DIR *dir;
    struct dirent *ptr;
    dir = opendir(UBSAN_LOG_DIR);
    while ((ptr = readdir(dir)) != NULL) {
        if (strstr(ptr->d_name, UBSAN_LOG_TAG) != NULL) {
            char tmp[BUFFER_SIZE] = UBSAN_LOG_DIR;
            strcat(tmp, ptr->d_name);
            CheckCfiLog(tmp, pattern);
        }
    }
    closedir(dir);
}