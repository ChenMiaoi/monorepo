#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Copyright (c) 2021 Huawei Device Co., Ltd.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Description: Use ark to execute js files
"""

import argparse
import os
import platform
import json
import sys
import signal
import re
import fileinput
import subprocess
from utils import *
from config import *


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--ark-tool',
                        default=DEFAULT_ARK_TOOL,
                        required=False,
                        help="ark's binary tool")
    parser.add_argument('--ark-aot', action='store_true',
                        required=False,
                        help="Run test262 with aot")
    parser.add_argument('--ark-aot-tool',
                        default=DEFAULT_ARK_AOT_TOOL,
                        required=False,
                        help="ark's aot tool")
    parser.add_argument("--libs-dir",
                        default=DEFAULT_LIBS_DIR,
                        required=False,
                        help="The path collection of dependent so has been divided by':'")
    parser.add_argument("--js-file",
                        required=True,
                        help="js file")
    parser.add_argument('--ark-frontend',
                        default=DEFAULT_ARK_FRONTEND,
                        required=False,
                        nargs='?', choices=ARK_FRONTEND_LIST, type=str,
                        help="Choose one of them")
    parser.add_argument('--ark-frontend-binary',
                        default=DEFAULT_ARK_FRONTEND_BINARY,
                        required=False,
                        help="ark frontend conversion binary tool")
    parser.add_argument('--ark-arch',
                        default=DEFAULT_ARK_ARCH,
                        required=False,
                        nargs='?', choices=ARK_ARCH_LIST, type=str,
                        help="Choose one of them")
    parser.add_argument('--ark-arch-root',
                        default=DEFAULT_ARK_ARCH,
                        required=False,
                        help="the root path for qemu-aarch64 or qemu-arm")
    parser.add_argument('--opt-level',
                        default=DEFAULT_OPT_LEVEL,
                        required=False,
                        help="the opt level for es2abc")
    parser.add_argument('--es2abc-thread-count',
                        default=DEFAULT_ES2ABC_THREAD_COUNT,
                        required=False,
                        help="the thread count for es2abc")
    parser.add_argument('--merge-abc-binary',
                        default=DEFAULT_MERGE_ABC_BINARY,
                        required=False,
                        help="frontend merge abc binary tool")
    parser.add_argument('--merge-abc-mode',
                        default=DEFAULT_MERGE_ABC_MODE,
                        required=False,
                        help="run test for merge abc mode")
    parser.add_argument('--product-name',
                        default=DEFAULT_PRODUCT_NAME,
                        required=False,
                        help="ark's product name")
    arguments = parser.parse_args()
    return arguments


ICU_PATH = f"--icu-data-path={CODE_ROOT}/third_party/icu/ohos_icu4j/data"
if platform.system() == "Windows" :
    ICU_PATH = ICU_PATH.replace("/","\\")
ARK_TOOL = DEFAULT_ARK_TOOL
LIBS_DIR = DEFAULT_LIBS_DIR
ARK_AOT_TOOL = DEFAULT_ARK_AOT_TOOL
ARK_FRONTEND = DEFAULT_ARK_FRONTEND
ARK_FRONTEND_BINARY = DEFAULT_ARK_FRONTEND_BINARY
ARK_ARCH = DEFAULT_ARK_ARCH
PROTO_BIN_SUFFIX = "protoBin"


def output(retcode, msg):
    if retcode == 0:
        if msg != '':
            print(str(msg))
    elif retcode == -6:
        sys.stderr.write("Aborted (core dumped)")
    elif retcode == -4:
        sys.stderr.write("Aborted (core dumped)")
    elif retcode == -11:
        sys.stderr.write("Segmentation fault (core dumped)")
    elif msg != '':
        sys.stderr.write(str(msg))
    else:
        sys.stderr.write("Unknown Error: " + str(retcode))


def exec_command(cmd_args, timeout=DEFAULT_TIMEOUT):
    proc = subprocess.Popen(cmd_args,
                            stderr=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            close_fds=True,
                            start_new_session=True)
    cmd_string = " ".join(cmd_args)
    code_format = 'utf-8'
    if platform.system() == "Windows":
        code_format = 'gbk'

    try:
        (output_res, errs) = proc.communicate(timeout=timeout)
        ret_code = proc.poll()

        if errs.decode(code_format, 'ignore') != '':
            output(1, errs.decode(code_format, 'ignore'))
            return 1

        if ret_code and ret_code != 1:
            code = ret_code
            msg = f"Command {cmd_string}: \n"
            msg += f"error: {str(errs.decode(code_format,'ignore'))}"
        else:
            code = 0
            msg = str(output_res.decode(code_format, 'ignore'))

    except subprocess.TimeoutExpired:
        proc.kill()
        proc.terminate()
        os.kill(proc.pid, signal.SIGTERM)
        code = 1
        msg = f"Timeout:'{cmd_string}' timed out after' {str(timeout)} seconds"
    except Exception as err:
        code = 1
        msg = f"{cmd_string}: unknown error: {str(err)}"
    output(code, msg)
    return code

def print_command(cmd_args):
    sys.stderr.write("\n")
    sys.stderr.write(" ".join(cmd_args))
    sys.stderr.write("\n")

# for debug use, to keep aot file
def run_command(cmd_args):
    return subprocess.run(" ".join(cmd_args))

class ArkProgram():
    def __init__(self, args):
        self.args = args
        self.ark_tool = ARK_TOOL
        self.ark_aot = False
        self.ark_aot_tool = ARK_AOT_TOOL
        self.libs_dir = LIBS_DIR
        self.ark_frontend = ARK_FRONTEND
        self.ark_frontend_binary = ARK_FRONTEND_BINARY
        self.module_list = []
        self.dynamicImport_list = []
        self.js_file = ""
        self.module = False
        self.abc_file = ""
        self.arch = ARK_ARCH
        self.arch_root = ""
        self.opt_level = DEFAULT_OPT_LEVEL
        self.es2abc_thread_count = DEFAULT_ES2ABC_THREAD_COUNT
        self.merge_abc_binary = DEFAULT_MERGE_ABC_BINARY
        self.merge_abc_mode = DEFAULT_MERGE_ABC_MODE

    def proce_parameters(self):
        if self.args.ark_tool:
            self.ark_tool = self.args.ark_tool

        if self.args.ark_aot:
            self.ark_aot = self.args.ark_aot

        if self.args.ark_aot_tool:
            self.ark_aot_tool = self.args.ark_aot_tool

        if self.args.ark_frontend_binary:
            self.ark_frontend_binary = self.args.ark_frontend_binary

        if self.args.libs_dir:
            self.libs_dir = self.args.libs_dir

        if self.args.ark_frontend:
            self.ark_frontend = self.args.ark_frontend

        if self.args.opt_level:
            self.opt_level = self.args.opt_level

        if self.args.es2abc_thread_count:
            self.es2abc_thread_count = self.args.es2abc_thread_count

        if self.args.merge_abc_binary:
            self.merge_abc_binary = self.args.merge_abc_binary

        if self.args.merge_abc_mode:
            self.merge_abc_mode = self.args.merge_abc_mode

        self.module_list = MODULE_LIST

        self.dynamicImport_list = DYNAMIC_IMPORT_LIST

        self.js_file = self.args.js_file

        self.arch = self.args.ark_arch

        self.arch_root = self.args.ark_arch_root

    def check_compile_mode(self, file):
        with open(file, 'r', encoding='utf-8') as check_file:
            content_file = check_file.read()
            module_pattern = '((?:export|import)\s+(?:{[\s\S]+}|\*))|'
            module_pattern += '(export\s+(?:let|const|var|function|class|default))|'
            module_pattern += '(import\s+[\'\"].+[\'\"])'
            module_mode_list = re.findall(module_pattern, content_file)

            for module_mode in list(set(module_mode_list)):
                if len(module_mode[0]) != 0 or len(module_mode[1]) != 0 or \
                    len(module_mode[2]) != 0:
                    return True

        if "flags: [module]" in content_file or "/language/module-code/" in self.js_file:
            return True

        return False

    def get_all_skip_force_gc_tests(self):
        SKIP_FORCE_GC_LIST_FILES.append(TS2ABC_SKIP_FORCE_GC_LIST_FILE)

        for file in SKIP_FORCE_GC_LIST_FILES:
            with open(file) as jsonfile:
                json_data = json.load(jsonfile)
                for key in json_data:
                    FORCE_GC_SKIP_TESTS.extend(key["files"])

    def gen_dependency_proto(self, dependency):
        cmd_args = []
        output_file = os.path.splitext(dependency.replace(DATA_DIR, BASE_OUT_DIR))[0]
        output_abc = f"{output_file}.abc"
        frontend_tool = self.ark_frontend_binary
        merge_abc_binary = self.args.merge_abc_binary
        merge_abc_mode = self.merge_abc_mode
        compile_as_module = self.check_compile_mode(dependency)

        if self.ark_frontend == ARK_FRONTEND_LIST[0]:
            if merge_abc_mode != "0":
                cmd_args = ['node', '--expose-gc', frontend_tool, dependency,
                            '--output-proto', '--merge-abc']
            else:
                # for testing no-record-name abc
                cmd_args = ['node', '--expose-gc', frontend_tool, dependency,
                            '-o', output_abc]
            if compile_as_module:
                mod_opt_index = 6
                cmd_args.insert(mod_opt_index, "--modules")
        elif self.ark_frontend == ARK_FRONTEND_LIST[1]:
            if merge_abc_mode != "0":
                proto_bin_file = output_file + "." + PROTO_BIN_SUFFIX
                cmd_args = [frontend_tool, dependency, '--outputProto',
                            proto_bin_file, '--merge-abc']
            else:
                # for testing no-record-name abc
                cmd_args = [frontend_tool, dependency, '--output', output_abc]
            if compile_as_module:
                mod_opt_index = 4
                cmd_args.insert(mod_opt_index, "--module")
        proc = subprocess.Popen(cmd_args)
        proc.wait()

    def gen_apart_abc(self, dependencies):
        merge_abc_binary = self.args.merge_abc_binary
        retcode = 0
        for dependency in list(set(dependencies)):
            cmd_args = []
            output_file = os.path.splitext(dependency.replace(DATA_DIR, BASE_OUT_DIR))[0]
            output_abc = os.path.basename(f"{output_file}.abc")
            file_dir = os.path.split(self.js_file)[0]
            is_apart_abc_existed = os.path.exists(file_dir + "/" + output_abc)
            dependency_file_prefix = os.path.basename(dependency)[:-3]
            dependency_bin_file = '%s/%s.%s' % (file_dir,
                                                dependency_file_prefix, PROTO_BIN_SUFFIX)
            cmd_args = [merge_abc_binary, '--input', dependency_bin_file,
                        '--suffix', PROTO_BIN_SUFFIX, '--outputFilePath',
                        file_dir, '--output', output_abc]
            if not is_apart_abc_existed:
                retcode = exec_command(cmd_args)
        return retcode

    def gen_merged_abc(self, dependencies, file_name_pre, proto_bin_file):
        merge_abc_binary = self.args.merge_abc_binary
        file_dir = os.path.split(self.js_file)[0]
        proto_abc_file = ".".join([os.path.splitext(os.path.basename(self.js_file))[0], "abc"])
        generate_merged_abc = True
        # collect protoBin file into new-made testcase dir
        if (len(dependencies) != 0):
            if os.path.exists(file_name_pre):
                subprocess.run(['rm', '-rf', file_name_pre])
            subprocess.run(['mkdir', file_name_pre])

            for dependency in list(set(dependencies)):
                dependency_file_prefix = os.path.basename(dependency)[:-3]
                dependency_bin_file = '%s/%s.%s' % (file_dir,
                                                    dependency_file_prefix, PROTO_BIN_SUFFIX)
                # test262 report syntax error cases
                if not os.path.exists(dependency_bin_file):
                    generate_merged_abc = False
                else:
                    subprocess.run(['cp', dependency_bin_file, file_name_pre])

            if not os.path.exists(proto_bin_file):
                generate_merged_abc = False
            else:
                subprocess.run(['cp', proto_bin_file, file_name_pre])

        if (len(dependencies) != 0) and generate_merged_abc:
            # module test262 cases
            cmd_args = [merge_abc_binary, '--input', file_name_pre,
                        '--suffix', PROTO_BIN_SUFFIX, '--outputFilePath',
                        file_dir, '--output', proto_abc_file]
            self.abc_file = f'{file_name_pre}.abc'
            return exec_command(cmd_args)
        elif os.path.exists(proto_bin_file):
            cmd_args = [merge_abc_binary, '--input', proto_bin_file,
                        '--suffix', PROTO_BIN_SUFFIX, '--outputFilePath',
                        file_dir, '--output', proto_abc_file]
            self.abc_file = f'{file_name_pre}.abc'
            return exec_command(cmd_args)
        return 0

    def gen_abc(self):
        js_file = self.js_file
        file_name_pre = os.path.splitext(js_file)[0]
        file_name = os.path.basename(js_file)
        file_dir = os.path.split(js_file)[0]
        out_file = f"{file_name_pre}.abc"
        out_proto = f"{file_name_pre}.proto"
        proto_bin_file = file_name_pre + "." + PROTO_BIN_SUFFIX
        self.abc_file = out_file
        mod_opt_index = 0
        compile_as_module = False
        cmd_args = []
        dependency_cmd_args = []
        frontend_tool = self.ark_frontend_binary
        merge_abc_mode = self.merge_abc_mode
        dependencies = []
        merge_abc_binary = self.args.merge_abc_binary
        retcode = 0

        # pre-generate the dependencies' abc when ark_frontend is [es2panda]
        if (file_name in self.module_list or file_name in self.dynamicImport_list):
            if ("dynamic-import" in js_file):
                search_dir = os.path.dirname(js_file)
            else:
                search_dir = os.path.dirname(js_file.replace(BASE_OUT_DIR, DATA_DIR))
            dependencies = collect_module_dependencies(js_file, search_dir, [])
            compile_as_module = self.check_compile_mode(js_file)
            if (self.ark_frontend == ARK_FRONTEND_LIST[1]):
                if list(set(dependencies)):
                    for dependency in list(set(dependencies)):
                        dependency_file = os.path.basename(dependency)
                        dependency_name = os.path.splitext(dependency_file)[0]
                        out_dependency_pre = '%s/%s' % (file_dir, dependency_name)
                        out_dependency_proto = f"{out_dependency_pre}.protoBin"
                        is_dependency_proto_existed = os.path.exists(out_dependency_proto)
                        if not is_dependency_proto_existed:
                            self.gen_dependency_proto(dependency)

        if self.ark_frontend == ARK_FRONTEND_LIST[0]:
            mod_opt_index = 3
            if merge_abc_mode != "0":
                cmd_args = ['node', '--expose-gc', frontend_tool, js_file,
                            '--output-proto', '--merge-abc']
            else:
                # for testing no-record-name abc
                cmd_args = ['node', '--expose-gc', frontend_tool, js_file,
                            '-o', out_file]
            if compile_as_module:
                cmd_args.insert(mod_opt_index, "-m")
                self.module = True
        elif self.ark_frontend == ARK_FRONTEND_LIST[1]:
            mod_opt_index = 1
            if merge_abc_mode != "0":
                # '--merge-abc' is added due to 'merge-abc' is not opened as default in es2abc, should be removed later
                cmd_args = [frontend_tool, '--function-threads=' +
                            str(self.es2abc_thread_count), '--outputProto',
                            proto_bin_file, js_file, '--merge-abc', '--opt-level=' + str(self.opt_level)]
            else:
                # for testing no-record-name abc
                cmd_args = [frontend_tool, '--opt-level=' + str(self.opt_level),
                            '--function-threads=' +
                            str(self.es2abc_thread_count), '--output',
                            out_file, js_file]
            if compile_as_module:
                cmd_args.insert(mod_opt_index, "--module")
                self.module = True
        # get abc file list from import statement
        if merge_abc_mode == "0" and self.ark_aot and self.module:
            self.abc_file = os.path.abspath(out_file)
            js_dir = os.path.dirname(js_file)
            for line in fileinput.input(js_file):
                import_line = re.findall(r"^(?:ex|im)port.*\.js", line)
                if len(import_line):
                    import_file = re.findall(r"['\"].*\.js", import_line[0])
                    if len(import_file):
                        abc_file = import_file[0][1:].replace(".js", ".abc")
                        abc_file = os.path.abspath(f'{js_dir}/{abc_file}')
                        if self.abc_file.find(abc_file) < 0:
                            self.abc_file += f':{abc_file}'

        if not os.path.exists(out_proto):
            retcode = exec_command(cmd_args)
            if retcode == 1:
                return retcode
            self.abc_cmd = cmd_args

        if self.ark_frontend == ARK_FRONTEND_LIST[1]:
            if ("dynamic-import" in js_file and not os.path.exists(out_file)):
                file_dir = os.path.split(self.js_file)[0]
                proto_abc_file = ".".join([os.path.splitext(os.path.basename(self.js_file))[0], "abc"])
                cmd_args = [merge_abc_binary, '--input', proto_bin_file,
                            '--suffix', PROTO_BIN_SUFFIX, '--outputFilePath',
                            file_dir, '--output', proto_abc_file]
                retcode = exec_command(cmd_args)
                if retcode == 1:
                    return retcode
                self.abc_cmd = cmd_args

        if merge_abc_mode != "0":
            if "dynamic-import" in js_file:
                return self.gen_apart_abc(dependencies)
            else:
                return self.gen_merged_abc(dependencies, file_name_pre, proto_bin_file)

        return retcode

    def compile_aot(self):
        os.environ["LD_LIBRARY_PATH"] = self.libs_dir
        file_name_pre = os.path.splitext(self.js_file)[0]
        cmd_args = []
        if self.arch == ARK_ARCH_LIST[1]:
            cmd_args = [self.ark_aot_tool, ICU_PATH,
                        f'--compiler-target-triple=aarch64-unknown-linux-gnu',
                        f'--aot-file={file_name_pre}',
                        self.abc_file]
        elif self.arch == ARK_ARCH_LIST[2]:
            cmd_args = [self.ark_aot_tool, ICU_PATH,
                        f'--compiler-target-triple=arm-unknown-linux-gnu',
                        f'--aot-file={file_name_pre}',
                        self.abc_file]
        elif self.arch == ARK_ARCH_LIST[0]:
            cmd_args = [self.ark_aot_tool, ICU_PATH,
                        f'--aot-file={file_name_pre}',
                        self.abc_file]
        retcode = exec_command(cmd_args, 180000)
        if retcode:
            print_command(self.abc_cmd)
            print_command(cmd_args)

    def execute_aot(self):
        unforce_gc = False
        os.environ["LD_LIBRARY_PATH"] = self.libs_dir
        file_name_pre = os.path.splitext(self.js_file)[0]
        cmd_args = []
        if self.arch == ARK_ARCH_LIST[1]:
            qemu_tool = "qemu-aarch64"
            qemu_arg1 = "-L"
            qemu_arg2 = self.arch_root
            cmd_args = [qemu_tool, qemu_arg1, qemu_arg2, self.ark_tool,
                        ICU_PATH,
                        f'--aot-file={file_name_pre}',
                        f'{file_name_pre}.abc']
        elif self.arch == ARK_ARCH_LIST[2]:
            qemu_tool = "qemu-arm"
            qemu_arg1 = "-L"
            qemu_arg2 =  self.arch_root
            cmd_args = [qemu_tool, qemu_arg1, qemu_arg2, self.ark_tool,
                        ICU_PATH,
                        f'--aot-file={file_name_pre}',
                        f'{file_name_pre}.abc']
        elif self.arch == ARK_ARCH_LIST[0]:
            if file_name_pre in FORCE_GC_SKIP_TESTS:
                unforce_gc = True
            asm_arg1 = "--enable-force-gc=true"
            if unforce_gc:
                asm_arg1 = "--enable-force-gc=false"
            cmd_args = [self.ark_tool, ICU_PATH, asm_arg1,
                        f'--aot-file={file_name_pre}',
                        f'{file_name_pre}.abc']

        record_name = os.path.splitext(os.path.split(self.js_file)[1])[0]
        cmd_args.insert(-1, f'--entry-point={record_name}')
        retcode = exec_command(cmd_args)
        if retcode:
            print_command(cmd_args)
        return retcode

    def execute(self):
        unforce_gc = False
        if platform.system() == "Windows" :
            #add env path for cmd/powershell execute
            libs_dir = self.libs_dir.replace(":", ";")
            libs_dir = libs_dir.replace("/", "\\")
            os.environ["PATH"] = libs_dir + ";" + os.environ["PATH"]
        elif platform.system() == "Linux" :
            os.environ["LD_LIBRARY_PATH"] = self.libs_dir
        else :
            sys.exit(f" test262 on {platform.system()} not supported")
        file_name_pre = os.path.splitext(self.js_file)[0]
        # In the case of Windows, it is necessary to convert ' \\' to '/', otherwise there will be a crash or the file cannot be found
        # Maintain consistent interface path with DevEco Studio 
        if platform.system() == "Windows": 
            file_name_pre = file_name_pre.replace("\\","/")
        cmd_args = []
        if self.arch == ARK_ARCH_LIST[1]:
            qemu_tool = "qemu-aarch64"
            qemu_arg1 = "-L"
            qemu_arg2 = self.arch_root
            cmd_args = [qemu_tool, qemu_arg1, qemu_arg2, self.ark_tool,
                        ICU_PATH,
                        f'{file_name_pre}.abc']
        elif self.arch == ARK_ARCH_LIST[2]:
            qemu_tool = "qemu-arm"
            qemu_arg1 = "-L"
            qemu_arg2 =  self.arch_root
            cmd_args = [qemu_tool, qemu_arg1, qemu_arg2, self.ark_tool,
                        ICU_PATH,
                        f'{file_name_pre}.abc']
        elif self.arch == ARK_ARCH_LIST[0]:
            if file_name_pre in FORCE_GC_SKIP_TESTS:
                unforce_gc = True
            asm_arg1 = "--enable-force-gc=true"
            if unforce_gc:
                asm_arg1 = "--enable-force-gc=false"
            cmd_args = [self.ark_tool, ICU_PATH, asm_arg1,
                        f'{file_name_pre}.abc']

        record_name = os.path.splitext(os.path.split(self.js_file)[1])[0]
        cmd_args.insert(-1, f'--entry-point={record_name}')
        retcode = exec_command(cmd_args)
        if retcode:
            print_command(cmd_args)
        return retcode

    def is_legal_frontend(self):
        if self.ark_frontend not in ARK_FRONTEND_LIST:
            sys.stderr.write("Wrong ark front-end option")
            return False
        return True

    def execute_ark(self):
        self.proce_parameters()
        self.get_all_skip_force_gc_tests()
        if not self.is_legal_frontend():
            return
        if self.gen_abc():
            return
        if self.ark_aot:
            self.compile_aot()
            self.execute_aot()
        else:
            self.execute()

def main():
    args = parse_args()

    ark = ArkProgram(args)
    ark.execute_ark()


if __name__ == "__main__":
    sys.exit(main())
