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

#include "agent/tracing_impl.h"
#include "ecmascript/tests/test_helper.h"
#include "protocol_handler.h"

using namespace panda::ecmascript;
using namespace panda::ecmascript::tooling;

namespace panda::test {
class TracingImplTest : public testing::Test {
public:
    static void SetUpTestCase()
    {
        GTEST_LOG_(INFO) << "SetUpTestCase";
    }

    static void TearDownTestCase()
    {
        GTEST_LOG_(INFO) << "TearDownCase";
    }

    void SetUp() override
    {
        TestHelper::CreateEcmaVMWithScope(ecmaVm, thread, scope);
    }

    void TearDown() override
    {
        TestHelper::DestroyEcmaVMWithScope(ecmaVm, scope);
    }

protected:
    EcmaVM *ecmaVm {nullptr};
    EcmaHandleScope *scope {nullptr};
    JSThread *thread {nullptr};
};

HWTEST_F_L0(TracingImplTest, EndTest)
{
    ProtocolChannel *channel = nullptr;
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    DispatchResponse response = tracing->End();
    ASSERT_TRUE(response.GetMessage() == "End not support now.");
}

HWTEST_F_L0(TracingImplTest, GetCategoriesTest)
{
    ProtocolChannel *channel = nullptr;
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    std::vector<std::string> categories = {};
    DispatchResponse response = tracing->GetCategories(categories);
    ASSERT_TRUE(response.GetMessage() == "GetCategories not support now.");
}

HWTEST_F_L0(TracingImplTest, RecordClockSyncMarkerTest)
{
    ProtocolChannel *channel = nullptr;
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    std::string syncId;
    DispatchResponse response = tracing->RecordClockSyncMarker(syncId);
    ASSERT_TRUE(response.GetMessage() == "RecordClockSyncMarker not support now.");
}

HWTEST_F_L0(TracingImplTest, RequestMemoryDumpTest)
{
    ProtocolChannel *channel = nullptr;
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    auto params = std::make_unique<RequestMemoryDumpParams>();
    std::string dumpGuid;
    bool success = false;
    DispatchResponse response = tracing->RequestMemoryDump(std::move(params), dumpGuid, success);
    ASSERT_TRUE(response.GetMessage() == "RequestMemoryDump not support now.");
}

HWTEST_F_L0(TracingImplTest, StartTest)
{
    ProtocolChannel *channel = nullptr;
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    auto params = std::make_unique<StartParams>();
    DispatchResponse response = tracing->Start(std::move(params));
    ASSERT_TRUE(response.GetMessage() == "Start not support now.");
}

HWTEST_F_L0(TracingImplTest, DispatcherImplDispatchTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel =  new ProtocolHandler(callback, ecmaVm);
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    auto dispatcherImpl = std::make_unique<TracingImpl::DispatcherImpl>(channel, std::move(tracing));
    std::string msg = std::string() + R"({"id":0,"method":"Debugger.Test","params":{}})";;
    DispatchRequest request(msg);
    dispatcherImpl->Dispatch(request);
    ASSERT_TRUE(result.find("Unknown method: Test") != std::string::npos);
    msg = std::string() + R"({"id":0,"method":"Debugger.end","params":{}})";
    DispatchRequest request1 = DispatchRequest(msg);
    dispatcherImpl->Dispatch(request1);
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("End not support now.") != std::string::npos);
}

HWTEST_F_L0(TracingImplTest, DispatcherImplEndTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel =  new ProtocolHandler(callback, ecmaVm);
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    auto dispatcherImpl = std::make_unique<TracingImpl::DispatcherImpl>(channel, std::move(tracing));
    std::string msg = std::string() + R"({"id":0,"method":"Debugger.end","params":{}})";
        DispatchRequest request = DispatchRequest(msg);
    dispatcherImpl->Dispatch(request);
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("End not support now.") != std::string::npos);
}

HWTEST_F_L0(TracingImplTest, DispatcherImplGetCategoriesTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel =  new ProtocolHandler(callback, ecmaVm);
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    auto dispatcherImpl = std::make_unique<TracingImpl::DispatcherImpl>(channel, std::move(tracing));
    std::string msg = std::string() + R"({"id":0,"method":"Debugger.getCategories","params":{}})";
        DispatchRequest request = DispatchRequest(msg);
    dispatcherImpl->Dispatch(request);
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("GetCategories not support now") != std::string::npos);
}

HWTEST_F_L0(TracingImplTest, DispatcherImplRecordClockSyncMarkerTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel =  new ProtocolHandler(callback, ecmaVm);
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    auto dispatcherImpl = std::make_unique<TracingImpl::DispatcherImpl>(channel, std::move(tracing));
    std::string msg = std::string() + R"({"id":0,"method":"Debugger.recordClockSyncMarker","params":{}})";
        DispatchRequest request = DispatchRequest(msg);
    dispatcherImpl->Dispatch(request);
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("RecordClockSyncMarker not support now.") != std::string::npos);
}

HWTEST_F_L0(TracingImplTest, DispatcherImplRequestMemoryDumpTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel =  new ProtocolHandler(callback, ecmaVm);
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    auto dispatcherImpl = std::make_unique<TracingImpl::DispatcherImpl>(channel, std::move(tracing));
    std::string msg = std::string() + R"({"id":0,"method":"Debugger.requestMemoryDump","params":{}})";
        DispatchRequest request = DispatchRequest(msg);
    dispatcherImpl->Dispatch(request);
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("RequestMemoryDump not support now.") != std::string::npos);
}

HWTEST_F_L0(TracingImplTest, DispatcherImplStartDumpTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel =  new ProtocolHandler(callback, ecmaVm);
    auto tracing = std::make_unique<TracingImpl>(ecmaVm, channel);
    auto dispatcherImpl = std::make_unique<TracingImpl::DispatcherImpl>(channel, std::move(tracing));
    std::string msg = std::string() + R"({"id":0,"method":"Debugger.start","params":{}})";
        DispatchRequest request = DispatchRequest(msg);
    dispatcherImpl->Dispatch(request);
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("Start not support now.") != std::string::npos);
}

HWTEST_F_L0(TracingImplTest, FrontendBufferUsageTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel = nullptr;
    auto frontend = std::make_unique<TracingImpl::Frontend>(channel);
    frontend->BufferUsage();
    ASSERT_TRUE(result == "");
    if (!channel) {
        channel =  new ProtocolHandler(callback, ecmaVm);
    }
    auto frontend1 = std::make_unique<TracingImpl::Frontend>(channel);
    frontend1->BufferUsage();
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("Tracing.BufferUsage") != std::string::npos);
}


HWTEST_F_L0(TracingImplTest, FrontendDataCollectedTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel = nullptr;
    auto frontend = std::make_unique<TracingImpl::Frontend>(channel);
    frontend->DataCollected();
    ASSERT_TRUE(result == "");
    if (!channel) {
        channel =  new ProtocolHandler(callback, ecmaVm);
    }
    auto frontend1 = std::make_unique<TracingImpl::Frontend>(channel);
    frontend1->DataCollected();
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("Tracing.DataCollected") != std::string::npos);
}

HWTEST_F_L0(TracingImplTest, FrontendTracingCompleteTest)
{
    std::string result = "";
    std::function<void(const void*, const std::string &)> callback =
        [&result]([[maybe_unused]] const void *ptr, const std::string &temp) { result = temp; };
    ProtocolChannel *channel = nullptr;
    auto frontend = std::make_unique<TracingImpl::Frontend>(channel);
    frontend->TracingComplete();
    ASSERT_TRUE(result == "");
    if (!channel) {
        channel =  new ProtocolHandler(callback, ecmaVm);
    }
    auto frontend1 = std::make_unique<TracingImpl::Frontend>(channel);
    frontend1->TracingComplete();
    if (channel) {
        delete channel;
        channel = nullptr;
    }
    ASSERT_TRUE(result.find("Tracing.TracingComplete") != std::string::npos);
}
}  // namespace panda::test