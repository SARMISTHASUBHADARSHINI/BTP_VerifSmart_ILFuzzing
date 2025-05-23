import subprocess

output_file = "result.txt"

with open(output_file, "a") as f_out:
    for depth in range(20, 21):
        print(f"Running with depth = {depth}")
        command = [
            "python3", "-m", "ilf",
            "--proj", "./example/crowdsale/",
            "--contract", "Crowdsale",
            "--fuzzer", "sym_plus",
            "--model", "./model/",
            "--limit", "2000",
            "--depth", str(depth),
            "--runs", "5"
        ]
        try:
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            output_lines = result.stdout.strip().splitlines()
        except Exception as e:
            f_out.write(f"Depth {depth}: Error occurred - {e}\n\n")
