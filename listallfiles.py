import os

def list_lean_files_alphabetically(root_dir: str, output_file: str):
    lean_files = []

    # Traverse the directory tree
    for dirpath, _, filenames in os.walk(root_dir):
        for filename in filenames:
            if filename.endswith(".lean"):
                full_path = os.path.join(dirpath, filename)
                lean_files.append(os.path.relpath(full_path, root_dir))

    # Sort alphabetically (case-insensitive)
    lean_files.sort(key=lambda x: x.lower())

    # Write results to a log file
    with open(output_file, 'w', encoding='utf-8') as f:
        for path in lean_files:
            f.write(path + '\n')

# Example usage
if __name__ == "__main__":
    root_directory = "FLT"  # Replace with your target directory
    output_log_file = "lean_files.log"
    list_lean_files_alphabetically(root_directory, output_log_file)
    print(f"output: FLT >> {output_log_file}")
