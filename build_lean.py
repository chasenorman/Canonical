#!/usr/bin/env python3
import subprocess
import shutil
import os
import platform

SYSTEM = platform.system()

def name_to_shared_lib(name):
    if SYSTEM == "Windows":
        return f"{name}.dll"
    elif SYSTEM == "Darwin":
        return f"lib{name}.dylib"
    else:
        return f"lib{name}.so"

LEAN_LIB = os.path.join("lean", ".lake", "packages", "Canonical", ".lake", "build", "lib", name_to_shared_lib("canonical"))

if SYSTEM == "Windows":
    TARGET = os.path.join("target", "x86_64-pc-windows-gnu", "release", name_to_shared_lib("canonical"))
else:
    TARGET = os.path.join("target", "release", name_to_shared_lib("canonical"))

def main():
    if SYSTEM == "Windows":
        subprocess.run(["cargo", "build", "-p", "canonical", "--release", "--target", "x86_64-pc-windows-gnu"], shell=False, check=True)
    else:
        subprocess.run(["cargo", "build", "-p", "canonical", "--release"], shell=False, check=True)
    shutil.copy2(TARGET, LEAN_LIB)
    
if __name__ == "__main__":
    main()
