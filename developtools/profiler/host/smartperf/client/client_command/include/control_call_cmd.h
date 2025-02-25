/*
 * Copyright (C) 2021 Huawei Device Co., Ltd.
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef CONTROL_CALL_CMD_H
#define CONTROL_CALL_CMD_H
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
namespace OHOS {
namespace SmartPerf {
class ControlCallCmd {
public:
    double ColdStart(std::vector<std::string> v);
    double ColdStartHM(std::vector<std::string> v);
    double HotStart(std::vector<std::string> v);
    double CompleteTime();
    double ResponseTime();
    double StartResponse(std::vector<std::string> v);
    static std::string SlideFPS(std::vector<std::string> v);
    static std::string SlideFps(std::vector<std::string> v);
    double PageFps();
    double StartFrameFps(std::vector<std::string> v);
    std::string GetResult(int argc, std::vector<std::string> v);
private:
    bool isOhTest = false;
    std::string result = "";
    int ohType = 5;
    int typeName = 2;
    double time = 0.0;
    double noNameType = -1.0;
};
}
}
#endif // SMARTPERF_COMMAND_H