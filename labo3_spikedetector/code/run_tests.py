import pathlib
import time
import subprocess
import os
import sys

SCRIPT_PATH = pathlib.Path(__file__).parent.resolve()
FPGA_SIM_DIR = os.path.join(SCRIPT_PATH, "fpga_sim")
UNIT_TESTS_DIR = os.path.join(SCRIPT_PATH, "embedded_soft", "test", "unit")
UNIT_TESTS_BUILD_DIR = os.path.join(UNIT_TESTS_DIR, "build")

INTEGRATION_TESTS_DIR = os.path.join(
    SCRIPT_PATH, "embedded_soft", "test", "integration"
)
INTEGRATION_TESTS_BUILD_DIR = os.path.join(INTEGRATION_TESTS_DIR, "build")


def launch_process(command, working_dir, env=None, shell=False):
    return subprocess.Popen(
        command,
        shell=shell,
        cwd=working_dir,
        env=os.environ.copy() if env is None else env,
    )


def launch_process_pipe(command, working_dir, env=None):
    return subprocess.Popen(
        command,
        cwd=working_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=os.environ.copy() if env is None else env,
    )


def launch_vsim(server_port):
    command = [os.path.join(FPGA_SIM_DIR, "arun.sh"), "-tool", "questa"]
    env = os.environ.copy()
    env["SERVER_PORT"] = str(server_port)
    env["PROJ_HOME"] = FPGA_SIM_DIR
    return launch_process_pipe(command, FPGA_SIM_DIR, env)


def run_command(command, working_dir, env=None):
    p = launch_process(command, working_dir, env)
    status = p.wait()

    if status != 0:
        raise RuntimeError(f"{command[0]} Command Failed")


def run_integration_tests():
    print("Now Running Integration Tests. This may take a while ...")

    print("Running cmake")
    run_command(
        ["cmake", "-S", ".", "-B", INTEGRATION_TESTS_BUILD_DIR], INTEGRATION_TESTS_DIR
    )

    print("Building")
    run_command(
        ["cmake", "--build", INTEGRATION_TESTS_BUILD_DIR], INTEGRATION_TESTS_BUILD_DIR
    )

    test_programs = [
        os.path.join(INTEGRATION_TESTS_BUILD_DIR, file)
        for file in os.listdir(INTEGRATION_TESTS_BUILD_DIR)
        if file.startswith("test_")
    ]
    print(f"Found {len(test_programs)} test programs")

    tests = []
    for program in test_programs:
        stdout, _ = launch_process_pipe(
            [program, "--gtest_list_tests"], INTEGRATION_TESTS_BUILD_DIR
        ).communicate()
        lines = stdout.decode().splitlines()
        if len(lines) == 0:
            print(f"WARNING Found 0 tests for {program}")
            continue

        current_test = ""
        for line in lines[1:]:
            stripped = line.strip()
            if stripped.endswith("."):
                current_test = stripped
            elif line.startswith("  "):
                test_case_name = current_test + stripped
                print(f"Found {test_case_name}")
                tests.append((program, test_case_name))

    ps = []
    for i, (test_program, test_name) in enumerate(tests):
        port = 8888 + i
        ps.append(
            (
                test_program,
                test_name,
                launch_process(
                    [
                        test_program,
                        f"--gtest_filter={test_name}",
                        "--gtest_color=yes",
                    ],
                    INTEGRATION_TESTS_BUILD_DIR,
                    env={"SERVER_PORT": str(port)},
                ),
                launch_vsim(port),
            )
        )

    ok = True
    for i, p in enumerate(ps):
        ret = p[2].wait()
        print(f"{p[0]} - {p[1]} - ", end=" ")
        p[3].kill()

        if ret != 0:
            ok = False
            print("ERROR")
        else:
            print("OK")

    return ok


def run_gtests(test_programs, cwd):
    ps = [
        (
            p,
            launch_process(
                [p, "--gtest_color=yes"],
                cwd,
            ),
        )
        for p in test_programs
    ]

    ok = True
    for p_name, p in ps:
        ret = p.wait()
        print(f"{p_name}", end=" ")
        if ret != 0:
            ok = False
            print("ERROR")
        else:
            print("OK")

    return ok


def run_unit_tests():
    print("Now Running Unit Tests")

    print("Running cmake")
    run_command(["cmake", "-S", ".", "-B", UNIT_TESTS_BUILD_DIR], UNIT_TESTS_DIR)

    print("Building")
    run_command(["cmake", "--build", UNIT_TESTS_BUILD_DIR], UNIT_TESTS_BUILD_DIR)

    test_programs = [
        file for file in os.listdir(UNIT_TESTS_BUILD_DIR) if file.startswith("test_")
    ]
    print(f"Found {len(test_programs)} test programs")

    return run_gtests(
        [os.path.join(UNIT_TESTS_BUILD_DIR, p) for p in test_programs],
        UNIT_TESTS_BUILD_DIR,
    )


def main():
    if not run_unit_tests():
        return 1

    if not run_integration_tests():
        return 1


if __name__ == "__main__":
    sys.exit(main())
