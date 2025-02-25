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

#ifndef ARKCOMPILER_TOOLCHAIN_CONNECT_SERVER_CONNECT_INSPECTOR_H
#define ARKCOMPILER_TOOLCHAIN_CONNECT_SERVER_CONNECT_INSPECTOR_H

#include <queue>
#include <string>
#include <unordered_map>
#include "connect_server.h"

namespace OHOS::ArkCompiler::Toolchain {
#ifdef __cplusplus
#if __cplusplus
extern "C" {
#endif
#endif /* End of #ifdef __cplusplus */

void StartServer(const std::string& componentName);

void StopServer([[maybe_unused]] const std::string& componentName);

void SendMessage(const std::string& message);

void StoreMessage(int32_t instanceId, const std::string& message);

void SendLayoutMessage(const std::string& message);

void StoreInspectorInfo(const std::string& jsonTreeStr,  const std::string& jsonSnapshotStr);

void RemoveMessage(int32_t instanceId);

bool WaitForConnection();

void SetSwitchCallBack(const std::function<void(bool)>& setSwitchStatus,
    const std::function<void(int32_t)>& createLayoutInfo, int32_t instanceId);

#ifdef __cplusplus
#if __cplusplus
}
#endif
#endif /* End of #ifdef __cplusplus */

struct LayoutInspectorInfo {
    std::string tree;
    std::string snapShot;
};

class ConnectInspector {
public:
    ConnectInspector() = default;
    ~ConnectInspector() = default;

    std::string componentName_;
    std::unordered_map<int32_t, std::string> infoBuffer_;
    LayoutInspectorInfo layoutInspectorInfo_;
    std::unique_ptr<ConnectServer> connectServer_;
    std::atomic<bool> waitingForDebugger_ = true;
    std::queue<std::string> ideMsgQueue_;
    std::function<void(bool)> setSwitchStatus_;
    std::function<void(int32_t)> createLayoutInfo_;
    int32_t instanceId_ = -1;
};
} // namespace OHOS::ArkCompiler::Toolchain

#endif // ARKCOMPILER_TOOLCHAIN_CONNECT_SERVER_CONNECT_INSPECTOR_H
