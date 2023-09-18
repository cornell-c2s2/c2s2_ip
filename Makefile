SHELL=/bin/bash -o pipefail
#==========================================
# c2s2_ip Makefile
#==========================================

#------------------------------------------
# ANSI Color Escape Defines
#------------------------------------------

RESET  =\033[0m

BLACK  =\033[0;30m
RED    =\033[0;31m
GREEN  =\033[0;32m
YELLOW =\033[0;33m
BLUE   =\033[0;34m
PURPLE =\033[0;35m
CYAN   =\033[0;36m
WHITE  =\033[0;37m

--parse-name:
	@printf "${CYAN}"
	@printf "Checking IP Name is set...\n"
ifndef IP
	@printf "${RED}"
	@printf "[ERROR] Looks like you didn't specify a name for the IP!\n"
	@printf "[ERROR] Try running 'make check-ip IP=<name>' or 'make new-ip IP=<name>' instead,\n"
	@printf "[ERROR] replacing <name> with your desired IP name\n"
	@exit 1
else
	@mkdir -p build
	@set -o pipefail
	@python tools/parse-ip-name.py ${IP} | tee /dev/tty | tail -n 1 > build/ip_name.txt
	@set +o pipefail
endif

clean:
	@printf "${CYAN} Cleaning up build directory...${RESET}\n"
	@rm -rf build/* || true
	@printf "${GREEN} - Done!${RESET}\n"

IP_NAME_PARSED = $(shell cat build/ip_name.txt)

# Recipe to check whether an IP already exists
check-ip: --parse-name
	@printf "${CYAN}"
	@printf "Checking for IP already named %s...\n" ${IP_NAME_PARSED}
	@if [ -d "src/${IP_NAME_PARSED}" ]; then \
		printf "${RED}" \
		printf "[ERROR] This IP already exists!\n" \
		printf "[ERROR] Please choose a different name\n" \
		printf "[ERROR] (Check if you have a branch with this name in the src directory)\n" \
		exit 1; \
	fi
	@printf "${GREEN}"
	@printf " - No similar-named IP exists!\n"

# Recipe for making new IP
new-ip: check-ip
	@printf "${PURPLE}"
	@printf "========================================\n"
	@printf "C2S2 IP CREATOR\n"
	@printf "========================================\n"
	@printf "${RESET}"

# Get name of IP
	@printf "${GREEN}"
	@printf " - IP Name Set to ${IP_NAME_PARSED}\n"

# Check if already used
	@printf "${CYAN}"
	@printf "Checking previously-existing IP...\n"
ifeq (${IP_USED},1)
	@printf "${RED}"
	@printf "[ERROR] A similar-named IP already exists!\n"
	@printf "[ERROR] Please choose a different name\n"
	@printf "[ERROR] (Use 'git branch -a' to see all of the existing\n"
	@printf "[ERROR] branches, corresponding to existing IP)\n"
else
	@printf "${GREEN}"
	@printf " - No similar-named IP exists!\n"

# Create new IP directory

	@printf "${CYAN}"
	@printf "Creating starter IP\n"

	@python tools/new_ip.py ${IP_NAME_PARSED}

# Make a new branch for the IP
	@printf "${CYAN}"
	@printf "Creating new IP branch...\n"
	
	@printf "${RESET}"
#	@git checkout -b ${IP_NAME_PARSED}

	@printf "${CYAN}"
	@printf "Updating remote...\n"

	@printf "${RESET}"
#	@git add .
#	@git commit -m "Initial IP: ${IP_NAME_PARSED}"
#	@git push --set-upstream origin ${IP_NAME_PARSED}

	@printf "${GREEN}"
	@printf "[SUCCESS] New IP successfully created!\n"

endif

lint:
	tools/lint.sh

INCLUDE = "."
test:
	@mkdir -p build
ifndef IP
	@pytest -k ${INCLUDE}
else
	@pytest src/${IP} -k ${INCLUDE}
endif

# Redundant rules to help with user typos
new_ip: new-ip
check_ip: check-ip