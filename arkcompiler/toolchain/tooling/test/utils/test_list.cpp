/*
 * Copyright (c) 2021 Huawei Device Co., Ltd.
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

#include "test/utils/test_list.h"

#include "test/utils/test_util.h"

// testcase list
#include "test/testcases/js_breakpoint_test.h"
#include "test/testcases/js_breakpoint_arrow_test.h"
#include "test/testcases/js_breakpoint_async_test.h"
#include "test/testcases/js_exception_test.h"
#include "test/testcases/js_range_error_test.h"
#include "test/testcases/js_single_step_test.h"
#include "test/testcases/js_step_into_test.h"
#include "test/testcases/js_step_over_test.h"
#include "test/testcases/js_step_out_test.h"
#include "test/testcases/js_syntax_exception_test.h"
#include "test/testcases/js_throw_exception_test.h"
#include "test/testcases/js_variable_first_test.h"
#include "test/testcases/js_variable_second_test.h"
#include "test/testcases/js_module_variable_test.h"
#include "test/testcases/js_dropframe_test.h"
#include "test/testcases/js_local_variable_scope_test.h"
#include "test/testcases/js_container_test.h"
#include "test/testcases/js_closure_scope_test.h"

namespace panda::ecmascript::tooling::test {
static std::string g_currentTestName = "";

static void RegisterTests()
{
    // Register testcases
    TestUtil::RegisterTest("JsExceptionTest", GetJsExceptionTest());
    TestUtil::RegisterTest("JsSingleStepTest", GetJsSingleStepTest());
    TestUtil::RegisterTest("JsBreakpointTest", GetJsBreakpointTest());
    TestUtil::RegisterTest("JsBreakpointAsyncTest", GetJsBreakpointAsyncTest());
    TestUtil::RegisterTest("JsBreakpointArrowTest", GetJsBreakpointArrowTest());
    TestUtil::RegisterTest("JsRangeErrorTest", GetJsRangeErrorTest());
    TestUtil::RegisterTest("JsSyntaxExceptionTest", GetJsSyntaxExceptionTest());
    TestUtil::RegisterTest("JsThrowExceptionTest", GetJsThrowExceptionTest());
    TestUtil::RegisterTest("JsStepIntoTest", GetJsStepIntoTest());
    TestUtil::RegisterTest("JsStepOverTest", GetJsStepOverTest());
    TestUtil::RegisterTest("JsStepOutTest", GetJsStepOutTest());
    TestUtil::RegisterTest("JSDropFrameTest", GetJsDropFrameTest());
    TestUtil::RegisterTest("JsVariableFirstTest", GetJsVariableFirstTest());
    TestUtil::RegisterTest("JsVariableSecondTest", GetJsVariableSecondTest());
    TestUtil::RegisterTest("JsModuleVariableTest", GetJsModuleVariableTest());
    TestUtil::RegisterTest("JsLocalVariableScopeTest", GetJsLocalVariableScopeTest());
    TestUtil::RegisterTest("JsContainerTest", GetJsContainerTest());
    TestUtil::RegisterTest("JsClosureScopeTest", GetJsClosureScopeTest());
}

static void RegisterCInterpTests()
{
    TestUtil::RegisterTest("JSDropFrameTest", GetJsDropFrameTest());
}

std::vector<const char *> GetTestList()
{
    RegisterTests();
    std::vector<const char *> res;

    auto &tests = TestUtil::GetTests();
    for (const auto &entry : tests) {
        res.push_back(entry.first.c_str());
    }
    return res;
}

std::vector<const char *> GetCInterpTestList()
{
    RegisterCInterpTests();
    std::vector<const char *> res;

    auto &tests = TestUtil::GetTests();
    for (const auto &entry : tests) {
        res.push_back(entry.first.c_str());
    }
    return res;
}

void SetCurrentTestName(const std::string &testName)
{
    g_currentTestName = testName;
}

std::string GetCurrentTestName()
{
    return g_currentTestName;
}

std::pair<std::string, std::string> GetTestEntryPoint(const std::string &testName)
{
    return TestUtil::GetTest(testName)->GetEntryPoint();
}
}  // namespace panda::ecmascript::tooling::test
