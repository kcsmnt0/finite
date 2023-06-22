#!/usr/bin/python3

import os
import os.path

print("module Everything where")
print()

for root, dirs, files in os.walk("src"):
    # for file in filter(lambda file: file.endswith(".agda"), files):
    for file in files:
        if file.endswith(".agda") and not file == "Everything.agda":
            print("import " + os.path.normpath(os.path.join(
                os.path.relpath(root, start="src"),
                os.path.splitext(os.path.basename(file))[0]
            )).replace('/','.'))
