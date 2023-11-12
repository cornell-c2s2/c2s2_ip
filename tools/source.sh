source ~/.bashrc

# Run setup-c2s2.sh if we are on the ecelinux machine
if [ -f /classes/c2s2/setup-c2s2.sh ]; then
  source setup-c2s2.sh
fi

export PYTHONPATH=$PYTHONPATH:$(pwd)

conda activate ./venv

echo -e "\033[0;32mC2S2 Workspace Initialized.\033[0m"