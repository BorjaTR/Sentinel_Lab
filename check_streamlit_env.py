#!/usr/bin/env python3
"""Check cocotb installation from Streamlit's perspective"""
import sys
import os

print("=" * 60)
print("Python executable:", sys.executable)
print("=" * 60)

print("\nPython path:")
for p in sys.path:
    print(f"  {p}")

print("\n" + "=" * 60)
print("Trying to import cocotb...")
try:
    import cocotb
    print(f"✓ cocotb found at: {cocotb.__file__}")

    makefile_path = os.path.join(
        os.path.dirname(cocotb.__file__),
        'share',
        'makefiles'
    )
    print(f"  Makefiles should be at: {makefile_path}")
    print(f"  Directory exists: {os.path.exists(makefile_path)}")

    if os.path.exists(makefile_path):
        files = os.listdir(makefile_path)
        print(f"  Files: {files}")

except ImportError as e:
    print(f"✗ cocotb NOT found: {e}")

print("=" * 60)
