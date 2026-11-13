#!/usr/bin/env python3
import subprocess
import shutil
import os
import platform

SYSTEM = platform.system()
CRATE_NAME = "canonical-agda"
LIB_NAME = "canonical_agda"

def name_to_shared_lib(name):
    if SYSTEM == "Windows":
        return f"{name}.dll"
    elif SYSTEM == "Darwin":
        return f"lib{name}.dylib"
    else:
        return f"lib{name}.so"

# Agda loads the library at runtime, from AGDA_CANONICAL_LIB or the search path.
AGDA_LIB_DIR = "lib"
AGDA_LIB = os.path.join(AGDA_LIB_DIR, name_to_shared_lib(LIB_NAME))

if SYSTEM == "Windows":
    TARGET = os.path.join("target", "x86_64-pc-windows-gnu", "release", name_to_shared_lib(LIB_NAME))
else:
    TARGET = os.path.join("target", "release", name_to_shared_lib(LIB_NAME))

def main():
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    if SYSTEM == "Windows":
        subprocess.run(["cargo", "build", "-p", CRATE_NAME, "--release", "--target", "x86_64-pc-windows-gnu"], shell=False, check=True)
    else:
        subprocess.run(["cargo", "build", "-p", CRATE_NAME, "--release"], shell=False, check=True)
    os.makedirs(AGDA_LIB_DIR, exist_ok=True)
    shutil.copy2(TARGET, AGDA_LIB)

if __name__ == "__main__":
    main()
