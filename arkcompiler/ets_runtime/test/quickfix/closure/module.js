/*
 * Copyright (c) 2022 Huawei Device Co., Ltd.
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

var e2 = -1

function A1() {
    var a1 = 1
    function B1() {
        var b1 = 11
        function C1() {
            print("base: " + e2)
            print("base: " + a1)
            print("base: " + b1)
        }
        C1()
    }
    B1()
}

globalThis.A1 = A1
