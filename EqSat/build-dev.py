# Build eqsat using the `dev` profile and copy content over to the release folder
import argparse, os, shutil, subprocess, sys, glob

ap = argparse.ArgumentParser()
ap.add_argument("--profile", default="dev")
ap.add_argument("--clean", action="store_true")
args = ap.parse_args()

os.chdir(os.path.dirname(os.path.abspath(__file__)))

if args.clean:
    subprocess.run(["cargo", "clean"], check=True)

subprocess.run(["cargo", "build", "--profile", args.profile], check=True)

src = "target/debug" if args.profile == "dev" else f"target/{args.profile}"
dst = "target/release"
os.makedirs(dst, exist_ok=True)

patterns = ["eq_sat.dll", "eq_sat.pdb", "eq_sat.dll.lib", "eq_sat.dll.exp", "libeq_sat.*"]
for pat in patterns:
    for f in glob.glob(os.path.join(src, pat)):
        shutil.copy2(f, dst)
        print(f"Copied {os.path.basename(f)} to {dst}/")
