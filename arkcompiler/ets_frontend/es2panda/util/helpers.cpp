/*
 * Copyright (c) 2021 Huawei Device Co., Ltd.
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.Apache.Org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "helpers.h"

#include <es2panda.h>
#include <ir/base/classDefinition.h>
#include <ir/base/classProperty.h>
#include <ir/base/methodDefinition.h>
#include <ir/base/property.h>
#include <ir/base/scriptFunction.h>
#include <ir/base/spreadElement.h>
#include <ir/expressions/arrayExpression.h>
#include <ir/expressions/assignmentExpression.h>
#include <ir/expressions/functionExpression.h>
#include <ir/expressions/identifier.h>
#include <ir/expressions/literals/booleanLiteral.h>
#include <ir/expressions/literals/numberLiteral.h>
#include <ir/expressions/literals/stringLiteral.h>
#include <ir/expressions/objectExpression.h>
#include <ir/expressions/unaryExpression.h>
#include <ir/statements/blockStatement.h>
#include <ir/statements/expressionStatement.h>
#include <ir/statements/variableDeclaration.h>
#include <ir/statements/variableDeclarator.h>
#include <ir/ts/tsParameterProperty.h>
#include <lexer/token/sourceLocation.h>
#include <parser/module/sourceTextModuleRecord.h>
#include <util/concurrent.h>

#ifdef ENABLE_BYTECODE_OPT
#include <bytecode_optimizer/bytecodeopt_options.h>
#include <bytecode_optimizer/optimize_bytecode.h>
#else
#include <assembly-type.h>
#include <assembly-program.h>
#include <assembly-emitter.h>
#endif

#ifdef PANDA_TARGET_WINDOWS
#include <windows.h>
#undef ERROR
#else
#include <unistd.h>
#endif
#include <fstream>
#include <iostream>

namespace panda::es2panda::util {

// Helpers

bool Helpers::IsGlobalIdentifier(const util::StringView &str)
{
    return (str.Is("NaN") || str.Is("undefined") || str.Is("Infinity"));
}

bool Helpers::ContainSpreadElement(const ArenaVector<ir::Expression *> &args)
{
    return std::any_of(args.begin(), args.end(), [](const auto *it) { return it->IsSpreadElement(); });
}

util::StringView Helpers::LiteralToPropName(ArenaAllocator *allocator, const ir::Expression *lit)
{
    switch (lit->Type()) {
        case ir::AstNodeType::IDENTIFIER: {
            return lit->AsIdentifier()->Name();
        }
        case ir::AstNodeType::STRING_LITERAL: {
            return lit->AsStringLiteral()->Str();
        }
        case ir::AstNodeType::NUMBER_LITERAL: {
            return Helpers::ToStringView(allocator, lit->AsNumberLiteral()->Number());
        }
        case ir::AstNodeType::NULL_LITERAL: {
            return "null";
        }
        case ir::AstNodeType::BOOLEAN_LITERAL: {
            if (lit->AsBooleanLiteral()->Value()) {
                return "true";
            }
            return "false";
        }
        default: {
            UNREACHABLE();
        }
    }
}

bool Helpers::IsIndex(double number)
{
    if (number >= 0 && number < static_cast<double>(INVALID_INDEX)) {
        auto intNum = static_cast<uint32_t>(number);

        if (static_cast<double>(intNum) == number) {
            return true;
        }
    }

    return false;
}

static bool IsDigit(char c)
{
    return (c >= '0' && c <= '9');
}

int64_t Helpers::GetIndex(const util::StringView &str)
{
    const auto &s = str.Utf8();

    if (s.empty() || (*s.begin() == '0' && s.length() > 1)) {
        return INVALID_INDEX;
    }

    int64_t value = 0;
    for (const auto c : s) {
        if (!IsDigit(c)) {
            return INVALID_INDEX;
        }

        constexpr auto MULTIPLIER = 10;
        value *= MULTIPLIER;
        value += (c - '0');

        if (value >= INVALID_INDEX) {
            return INVALID_INDEX;
        }
    }

    return value;
}

bool Helpers::FileExtensionIs(std::string_view filePath, std::string_view extension)
{
    return filePath.length() > extension.length() && Helpers::EndsWith(filePath, extension);
}

bool Helpers::EndsWith(std::string_view str, std::string_view suffix)
{
    if (str.length() < suffix.length()) {
        return false;
    }
    size_t expectPos = str.length() - suffix.length();
    return str.find(suffix, expectPos) == expectPos;
}

void Helpers::GetScientificNotationForDouble(double number, uint32_t significandBitCount, int32_t &numberBitCount,
                                             char *significandArray, char *sciNotationArray, uint32_t size)
{
    if (size < MAX_DOUBLE_DIGIT) {
        std::cerr << "Failed to set the size of buffer in snprintf_s!" << std::endl;
        return;
    }
    if (snprintf_s(sciNotationArray, size, size - 1, "%.*e", significandBitCount - 1, number) == FAIL_SNPRINTF_S) {
        std::cerr << "Failed to write number to buffer in snprintf_s!" << std::endl;
        return;
    }

    // sciNotationArray includes significand, '.' and 'e'
    // If significandBitCount == 1, sciNotationArray does not contain '.'
    int32_t exponent = atoi(sciNotationArray + significandBitCount + 1 + (significandBitCount > 1));
    numberBitCount = exponent + 1;

    // Get the significand of the current sciNotationArray
    if (significandBitCount > 1) {
        for (uint32_t i = 0; i < significandBitCount + 1; i++) {
            significandArray[i] = sciNotationArray[i];
        }
    }

    significandArray[significandBitCount + 1] = '\0';
}

int32_t Helpers::GetIntegerSignificandBitCount(double number, int32_t &numberBitCount, char *significandArray)
{
    uint32_t bitPos = 0;
    uint32_t minBitPos = 1;
    uint32_t maxBitPos = MAX_DOUBLE_PRECISION_DIGIT;
    uint32_t integerAndPointBitCount = 2;
    char sciNotationArray[MAX_DOUBLE_DIGIT] = {0};

    while (minBitPos < maxBitPos) {
        bitPos = (minBitPos + maxBitPos) / 2; // 2: binary search
        GetScientificNotationForDouble(number, bitPos, numberBitCount, significandArray,
                                       sciNotationArray, sizeof(sciNotationArray));

        // Update bitPos
        if (std::strtod(sciNotationArray, nullptr) == number) {
            while (bitPos >= integerAndPointBitCount && significandArray[bitPos] == '0') {
                bitPos--;
            }
            maxBitPos = bitPos;
        } else {
            minBitPos = bitPos + 1;
        }
    }

    // minBitPos == maxBitPos
    bitPos = maxBitPos;
    GetScientificNotationForDouble(number, bitPos, numberBitCount, significandArray,
                                   sciNotationArray, sizeof(sciNotationArray));

    return bitPos;
}

std::string Helpers::DoubleToString(double number)
{
    // In Scientific notation, number is expressed in the form of significand multiplied by exponent-th power of 10.
    // The range of significand is: 1 <= |significand| < 10
    // Scientific notation of number: sciNotationArray = significand * (10 ** exponent)
    // number 1.23e25 => sciNotationArray: 1.23e+25, significand: 1.23, exponent: 25,

    // In the ECMAScript, integerSignificand, integerSignificandBitCount and numberBitCount are defined as an integer:
    // 1. integerSignificand is an integer in the Decimal representation of Scientific notation.
    // 2. integerSignificandBitCount is the number of bits in the Decimal representation of significand.
    // 3. numberBitCount is the number of bits in the Decimal representation of number.
    // Scientific notation of number in the ECMAScript of Number::toString (number):
    // integerSciNotationArray = integerSignificand * (10 ** (numberBitCount - integerSignificandBitCount))
    // number 1.23e25 => integerSciNotationArray: 123e+23, integerSignificand: 123, integerExponent: 23,
    //                   integerSignificandBitCount: 3, numberBitCount: 26
    std::string result;
    int32_t numberBitCount = 0;
    char significandArray[MAX_DOUBLE_DIGIT] = {0};

    if (number < 0) {
        result += "-";
        number = -number;
    }

    // The number of bits of significand in integer form
    int32_t integerSignificandBitCount = GetIntegerSignificandBitCount(number, numberBitCount, significandArray);

    std::string significand = significandArray;
    std::string integerSignificand;
    if (numberBitCount > 0 && numberBitCount <= MAX_DECIMAL_EXPONENT) {
        integerSignificand = significand.erase(1, 1);
        if (numberBitCount >= integerSignificandBitCount) {
            // If integerSignificandBitCount ≤ numberBitCount ≤ 21, return the string represented by Decimal,
            // integerSignificand followed by (numberBitCount - integerSignificandBitCount) digit zeros.
            integerSignificand += std::string(numberBitCount - integerSignificandBitCount, '0');
        } else {
            // If 0 < numberBitCount < integerSignificandBitCount, return the string represented by Decimal,
            // integerSignificand followed by point on the (numberBitCount + 1) digit.
            integerSignificand.insert(numberBitCount, 1, '.');
        }
    } else if (numberBitCount <= 0 && numberBitCount > MIN_DECIMAL_EXPONENT) {
        // If -6 < numberBitCount ≤ 0, return the string consisting of "0." and digit zeros represented by Decimal,
        // string followed by integerSignificand.
        integerSignificand = significand.erase(1, 1);
        integerSignificand = std::string("0.") + std::string(-numberBitCount, '0') + integerSignificand;
    } else {
        // If integerSignificandBitCount == 1, return the string consisting of the single digit of significand.
        if (integerSignificandBitCount == 1) {
            significand = significand.erase(1, 1);
        }
        // If numberBitCount ≤ -6 or numberBitCount > 21, return the string represented by Scientific notation,
        // integerSignificand followed by "e", symbol and (numberBitCount - 1) digit zeros.
        significand += 'e' + (numberBitCount >= 1 ? std::string("+") : "") + std::to_string(numberBitCount - 1);

        result += significand;
        return result;
    }

    result += integerSignificand;
    return result;
}

std::string Helpers::ToString(double number)
{
    if (std::isnan(number)) {
        return "NaN";
    }
    if (number == 0.0) {
        return "0";
    }
    if (std::isinf(number)) {
        return "Infinity";
    }

    std::string str;
    if (Helpers::IsInteger<int32_t>(number)) {
        str = std::to_string(static_cast<int32_t>(number));
    } else {
        str = DoubleToString(number);
    }

    return str;
}

util::StringView Helpers::ToStringView(ArenaAllocator *allocator, double number)
{
    util::UString str(ToString(number), allocator);
    return str.View();
}

util::StringView Helpers::ToStringView(ArenaAllocator *allocator, uint32_t number)
{
    ASSERT(number <= static_cast<uint32_t>(std::numeric_limits<int32_t>::max()));
    return ToStringView(allocator, static_cast<int32_t>(number));
}

util::StringView Helpers::ToStringView(ArenaAllocator *allocator, int32_t number)
{
    util::UString str(ToString(number), allocator);
    return str.View();
}

const ir::ScriptFunction *Helpers::GetContainingConstructor(const ir::AstNode *node)
{
    const ir::ScriptFunction *iter = GetContainingFunction(node);

    while (iter != nullptr) {
        if (iter->IsConstructor()) {
            return iter;
        }

        if (!iter->IsArrow()) {
            return nullptr;
        }

        iter = GetContainingFunction(iter);
    }

    return iter;
}

const ir::ScriptFunction *Helpers::GetContainingConstructor(const ir::ClassProperty *node)
{
    for (const auto *parent = node->Parent(); parent != nullptr; parent = parent->Parent()) {
        if (parent->IsClassDefinition()) {
            return parent->AsClassDefinition()->Ctor()->Function();
        }
    }

    return nullptr;
}

const ir::ScriptFunction *Helpers::GetContainingFunction(const ir::AstNode *node)
{
    for (const auto *parent = node->Parent(); parent != nullptr; parent = parent->Parent()) {
        if (parent->IsScriptFunction()) {
            return parent->AsScriptFunction();
        }
    }

    return nullptr;
}

const ir::ClassDefinition *Helpers::GetClassDefiniton(const ir::ScriptFunction *node)
{
    ASSERT(node->IsConstructor());
    ASSERT(node->Parent()->IsFunctionExpression());
    ASSERT(node->Parent()->Parent()->IsMethodDefinition());
    ASSERT(node->Parent()->Parent()->Parent()->IsClassDefinition());

    return node->Parent()->Parent()->Parent()->AsClassDefinition();
}

bool Helpers::IsSpecialPropertyKey(const ir::Expression *expr)
{
    if (!expr->IsStringLiteral()) {
        return false;
    }

    auto *lit = expr->AsStringLiteral();
    return lit->Str().Is("prototype") || lit->Str().Is("constructor");
}

bool Helpers::IsConstantPropertyKey(const ir::Expression *expr, bool isComputed)
{
    switch (expr->Type()) {
        case ir::AstNodeType::IDENTIFIER: {
            return !isComputed;
        }
        case ir::AstNodeType::NUMBER_LITERAL:
        case ir::AstNodeType::STRING_LITERAL:
        case ir::AstNodeType::BOOLEAN_LITERAL:
        case ir::AstNodeType::NULL_LITERAL: {
            return true;
        }
        default:
            break;
    }

    return false;
}

bool Helpers::IsConstantExpr(const ir::Expression *expr)
{
    switch (expr->Type()) {
        case ir::AstNodeType::NUMBER_LITERAL:
        case ir::AstNodeType::STRING_LITERAL:
        case ir::AstNodeType::BOOLEAN_LITERAL:
        case ir::AstNodeType::NULL_LITERAL: {
            return true;
        }
        default:
            break;
    }

    return false;
}

bool Helpers::IsBindingPattern(const ir::AstNode *node)
{
    return node->IsArrayPattern() || node->IsObjectPattern();
}

bool Helpers::IsPattern(const ir::AstNode *node)
{
    return node->IsArrayPattern() || node->IsObjectPattern() || node->IsAssignmentPattern();
}

static void CollectBindingName(const ir::AstNode *node, std::vector<const ir::Identifier *> *bindings)
{
    switch (node->Type()) {
        case ir::AstNodeType::IDENTIFIER: {
            if (!Helpers::IsGlobalIdentifier(node->AsIdentifier()->Name())) {
                bindings->push_back(node->AsIdentifier());
            }

            break;
        }
        case ir::AstNodeType::OBJECT_PATTERN: {
            for (const auto *prop : node->AsObjectPattern()->Properties()) {
                CollectBindingName(prop, bindings);
            }
            break;
        }
        case ir::AstNodeType::ARRAY_PATTERN: {
            for (const auto *element : node->AsArrayPattern()->Elements()) {
                CollectBindingName(element, bindings);
            }
            break;
        }
        case ir::AstNodeType::ASSIGNMENT_PATTERN: {
            CollectBindingName(node->AsAssignmentPattern()->Left(), bindings);
            break;
        }
        case ir::AstNodeType::PROPERTY: {
            CollectBindingName(node->AsProperty()->Value(), bindings);
            break;
        }
        case ir::AstNodeType::REST_ELEMENT: {
            CollectBindingName(node->AsRestElement()->Argument(), bindings);
            break;
        }
        default:
            break;
    }
}

std::vector<const ir::Identifier *> Helpers::CollectBindingNames(const ir::AstNode *node)
{
    std::vector<const ir::Identifier *> bindings;
    CollectBindingName(node, &bindings);
    return bindings;
}

util::StringView Helpers::FunctionName(ArenaAllocator *allocator, const ir::ScriptFunction *func)
{
    if (func->Id()) {
        return func->Id()->Name();
    }

    if (func->Parent()->IsFunctionDeclaration()) {
        return parser::SourceTextModuleRecord::DEFAULT_EXTERNAL_NAME;
    }

    const ir::AstNode *parent = func->Parent()->Parent();

    if (func->IsConstructor()) {
        parent = parent->Parent();
        if (parent->AsClassDefinition()->Ident()) {
            return parent->AsClassDefinition()->Ident()->Name();
        }

        parent = parent->Parent()->Parent();
    }

    switch (parent->Type()) {
        case ir::AstNodeType::VARIABLE_DECLARATOR: {
            const ir::VariableDeclarator *varDecl = parent->AsVariableDeclarator();

            if (varDecl->Id()->IsIdentifier()) {
                return varDecl->Id()->AsIdentifier()->Name();
            }

            break;
        }
        case ir::AstNodeType::METHOD_DEFINITION: {
            const ir::MethodDefinition *methodDef = parent->AsMethodDefinition();

            if (methodDef->Key()->IsIdentifier()) {
                return methodDef->Key()->AsIdentifier()->Name();
            }

            break;
        }
        case ir::AstNodeType::ASSIGNMENT_EXPRESSION: {
            const ir::AssignmentExpression *assignment = parent->AsAssignmentExpression();

            if (assignment->Left()->IsIdentifier()) {
                return assignment->Left()->AsIdentifier()->Name();
            }

            break;
        }
        case ir::AstNodeType::ASSIGNMENT_PATTERN: {
            const ir::AssignmentExpression *assignment = parent->AsAssignmentPattern();

            if (assignment->Left()->IsIdentifier()) {
                return assignment->Left()->AsIdentifier()->Name();
            }

            break;
        }
        case ir::AstNodeType::PROPERTY: {
            const ir::Property *prop = parent->AsProperty();

            if (prop->Kind() != ir::PropertyKind::PROTO &&
                Helpers::IsConstantPropertyKey(prop->Key(), prop->IsComputed())) {
                return Helpers::LiteralToPropName(allocator, prop->Key());
            }

            break;
        }
        case ir::AstNodeType::EXPORT_DEFAULT_DECLARATION: {
            return parser::SourceTextModuleRecord::DEFAULT_EXTERNAL_NAME;
        }
        default:
            break;
    }

    return util::StringView();
}

std::tuple<util::StringView, bool> Helpers::ParamName(ArenaAllocator *allocator, const ir::AstNode *param,
                                                      uint32_t index)
{
    switch (param->Type()) {
        case ir::AstNodeType::IDENTIFIER: {
            return {param->AsIdentifier()->Name(), false};
        }
        case ir::AstNodeType::ASSIGNMENT_PATTERN: {
            const auto *lhs = param->AsAssignmentPattern()->Left();
            if (lhs->IsIdentifier()) {
                return {param->AsAssignmentPattern()->Left()->AsIdentifier()->Name(), false};
            }
            break;
        }
        case ir::AstNodeType::REST_ELEMENT: {
            if (param->AsRestElement()->Argument()->IsIdentifier()) {
                return {param->AsRestElement()->Argument()->AsIdentifier()->Name(), false};
            }
            break;
        }
        case ir::AstNodeType::TS_PARAMETER_PROPERTY: {
            return ParamName(allocator, param->AsTSParameterProperty()->Parameter(), index);
        }
        default:
            break;
    }

    return {Helpers::ToStringView(allocator, index), true};
}

bool Helpers::IsChild(const ir::AstNode *parent, const ir::AstNode *child)
{
    while (child) {
        if (child == parent) {
            return true;
        }

        child = child->Parent();
    }

    return false;
}

bool Helpers::IsObjectPropertyValue(const ArenaVector<ir::Expression *> &properties, const ir::AstNode *ident)
{
    for (const auto *prop : properties) {
        if (prop->AsProperty()->Value() == ident) {
            return true;
        }
    }

    return false;
}

SignedNumberLiteral Helpers::GetSignedNumberLiteral(const ir::Expression *expr)
{
    if (!expr->IsUnaryExpression()) {
        return SignedNumberLiteral::UNRECOGNIZED;
    }

    auto unaryExpression = expr->AsUnaryExpression();
    if (!unaryExpression->Argument()->IsNumberLiteral()) {
        return SignedNumberLiteral::UNRECOGNIZED;
    }

    // TODO(hxw): Here we return different value for positive and nagative number literal in UnaryExpression.
    // Because when we access a computed property by MemberExpression, the compiler should emit different instruction.
    // Now es2abc always emits the instruction `loadObjByValue` whether the computed property is literal or not.
    // It can be optimized. For positive integer literal, the instruction should be `loadObjByIndex`.
    // While for negative number literal, the instruction should be `loadObjByName`.
    // So I add this util api and return different value for future use.
    if (unaryExpression->OperatorType() == lexer::TokenType::PUNCTUATOR_PLUS) {
        return SignedNumberLiteral::POSITIVE;
    } else if (unaryExpression->OperatorType() == lexer::TokenType::PUNCTUATOR_MINUS) {
        return SignedNumberLiteral::NEGATIVE;
    }

    return SignedNumberLiteral::UNRECOGNIZED;
}

void Helpers::OptimizeProgram(panda::pandasm::Program *prog,  const std::string &inputFile)
{
    // The possibility of handling variables that may not be used
    std::map<std::string, size_t> stat;
    [[maybe_unused]] std::map<std::string, size_t> *statp = &stat;
    panda::pandasm::AsmEmitter::PandaFileToPandaAsmMaps maps{};
    [[maybe_unused]] panda::pandasm::AsmEmitter::PandaFileToPandaAsmMaps *mapsp = &maps;

#ifdef PANDA_WITH_BYTECODE_OPTIMIZER
    const uint32_t COMPONENT_MASK = panda::Logger::Component::ASSEMBLER |
                                    panda::Logger::Component::BYTECODE_OPTIMIZER |
                                    panda::Logger::Component::COMPILER;
    panda::Logger::InitializeStdLogging(panda::Logger::Level::ERROR, COMPONENT_MASK);

    std::string pid;
#ifdef PANDA_TARGET_WINDOWS
    pid = std::to_string(GetCurrentProcessId());
#else
    pid = std::to_string(getpid());
#endif
    const std::string outputSuffix = ".unopt.abc";
    std::string tempOutput = panda::os::file::File::GetExtendedFilePath(inputFile + pid + outputSuffix);
    if (panda::pandasm::AsmEmitter::Emit(tempOutput, *prog, statp, mapsp, true)) {
        panda::bytecodeopt::OptimizeBytecode(prog, mapsp, tempOutput, true, true);
    }

    std::remove(tempOutput.c_str());
#endif
}

bool Helpers::ReadFileToBuffer(const std::string &file, std::stringstream &ss)
{
    std::ifstream inputStream = Helpers::FileStream<std::ifstream>(
        panda::os::file::File::GetExtendedFilePath(file), std::ios::binary);
    if (inputStream.fail()) {
        std::cerr << "Failed to read file to buffer: " << file << std::endl;
        return false;
    }
    ss << inputStream.rdbuf();
    return true;
}

void Helpers::ScanDirectives(ir::ScriptFunction *func, const lexer::LineIndex &lineIndex)
{
    auto *body = func->Body();
    if (!body || body->IsExpression()) {
        return;
    }

    auto &statements = body->AsBlockStatement()->Statements();
    if (statements.empty()) {
        return;
    }

    bool keepScan = true;
    auto iter = statements.begin();
    while (keepScan && (iter != statements.end())) {
        auto *stmt = *iter++;
        if (!stmt->IsExpressionStatement()) {
            return;
        }

        auto *expr = stmt->AsExpressionStatement()->GetExpression();
        if (!expr->IsStringLiteral()) {
            return;
        }

        keepScan = SetFuncFlagsForDirectives(expr->AsStringLiteral(), func, lineIndex);
    }

    return;
}

bool Helpers::SetFuncFlagsForDirectives(const ir::StringLiteral *strLit, ir::ScriptFunction *func,
                                        const lexer::LineIndex &lineIndex)
{
    if (strLit->Str().Is(SHOW_SOURCE)) {
        func->AddFlag(ir::ScriptFunctionFlags::SHOW_SOURCE);
        return true;
    }

    if (strLit->Str().Is(USE_CONCURRENT)) {
        util::Concurrent::SetConcurrent(func, strLit, lineIndex);
        return true;
    }

    return false;
}

std::string Helpers::GetHashString(std::string str)
{
    uint64_t result = FNV_OFFSET;

    const uint8_t *input = reinterpret_cast<const uint8_t *>(str.c_str());
    // FNV-1a 64-bit Algorithm
    for (size_t i = 0; i < str.size(); i++) {
        result ^= input[i];
        result *= FNV_PRIME;
    }

    return std::to_string(result);
}

#ifdef PANDA_TARGET_WINDOWS
std::wstring Helpers::Utf8ToUtf16(const std::string &utf8)
{
    std::wstring utf16;
    if (utf8.empty()) {
        return utf16;
    }

    if (utf8.length() > static_cast<size_t>(std::numeric_limits<int>::max())) {
        std::cerr << "Length of filename: " << utf8 << " is too long" << std::endl;
        return utf16;
    }

    const int utf8Length = static_cast<int>(utf8.length());
    constexpr DWORD kFlags = MB_ERR_INVALID_CHARS;
    const int utf16Length = MultiByteToWideChar(CP_UTF8, kFlags, utf8.data(), utf8Length, nullptr, 0);
    if (utf16Length == 0) {
        std::cerr << "The filename: " << utf8 << " is not a valid utf8 encoding string" << std::endl;
        return utf16;
    }

    utf16.resize(utf16Length);
    MultiByteToWideChar(CP_UTF8, kFlags, utf8.data(), utf8Length, &utf16[0], utf16Length);
    return utf16;
}
#endif

}  // namespace panda::es2panda::util
