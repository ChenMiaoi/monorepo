/*
 * Copyright (c) 2023 Huawei Device Co., Ltd.
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

declare function print(arg:any) : string;

function GenerateArray(): Int32Array {
    let resource: Int32Array = new Int32Array([12, 43, 56, 76, 89, 54, 45, 32, 35, 47, 46, 44, 21, 37, 84]);
    return resource;
}

function Foo(resources: number[], index: number) : number {
    let num = resources[index % resources.length];
    if (num % 2 == 0) {
        num += 2
    } else {
        num += 1
    }

    num = num / 2;
    return resources[index % resources.length] + num;
}
export function RunNormalCall():number {
    let res : number = 1;
    let resources : Int32Array = GenerateArray();
    for(let i=0;i<100;i++) {
        res = Foo(resources, i);
    }
    return res

}
let num = RunNormalCall()
print(num)