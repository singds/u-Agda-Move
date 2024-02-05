#!/bin/bash

# Check if a filename is provided as an argument
if [ $# -eq 0 ]; then
    echo "Usage: $0 <filename>"
    exit 1
fi

# Assign the filename to a variable
file="$1"

# Check if the file exists
if [ ! -e "$file" ]; then
    echo "The file $file does not exist."
    exit 1
fi

temp_script=$(mktemp)
awk '/{-/,/-}/ {if (/#!/) flag=1; if (flag && !/-}/) print} /-}/{flag=0}' "$file" > "$temp_script"

# Make the temporary script executable
chmod +x "$temp_script"

# Execute the temporary script on the same file
"$temp_script" "$file"

# Clean up the temporary script
rm -f "$temp_script"

echo "Script execution completed."