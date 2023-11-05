SHELL=/bin/bash -o pipefail
# ==============================================================================
# c2s2_ip Makefile
# ==============================================================================

# ------------------------------------------------------------------------------
# ANSI Color Escape Defines
# ------------------------------------------------------------------------------

RESET  =\033[0m

BLACK  =\033[0;30m
RED    =\033[0;31m
GREEN  =\033[0;32m
YELLOW =\033[0;33m
BLUE   =\033[0;34m
PURPLE =\033[0;35m
CYAN   =\033[0;36m
WHITE  =\033[0;37m

VENV:=. .venv/bin/activate

# Extra arguments to pass
EXTRA_ARGS=

# Pulls main branch
--pull:
	@printf "${CYAN}Getting Latest Updates...${RESET}\n"
	@git checkout main
	@git pull

vscode: 
	@printf "${CYAN}Installing VSCode Extensions...${RESET}\n"
	@cat .workspace-extensions | xargs code

.venv:
	@printf "${CYAN}Setting Up Virtual Environment...${RESET}\n"
	@python3 -m venv .venv
	@printf "${CYAN}Installing Python Dependencies...${RESET}\n"
	@$(VENV) && pip install --upgrade pip
	@$(VENV) && pip install -r requirements.txt
	@printf "${GREEN}Dependencies installed!${RESET}\n"
	@printf "${YELLOW}Run ${RED}source .venv/bin/activate${YELLOW} to activate your virtual environment.${RESET}\n"


install: --pull vscode .venv force-install-caravel

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
	@$(VENV) && python tools/parse-ip-name.py ${IP} | tee /dev/tty | tail -n 1 > build/ip_name.txt
endif

clean:
	@printf "${CYAN} Cleaning up build directories...${RESET}\n"
	@rm -rf build*/
	@printf "${CYAN} Cleaning up logs...${RESET}\n"
	@rm -rf log*/
	@printf "${GREEN} - Done!${RESET}\n"

IP_NAME_PARSED = $(shell cat build/ip_name.txt)

# ------------------------------------------------------------------------------
# CREATING IP
# ------------------------------------------------------------------------------

# Recipe to check whether an IP already exists
check-ip: --pull --parse-name
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
	@printf " - No similar-named IP exists!${RESET}\n"

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
	@printf "[ERROR] branches, corresponding to existing IP)${RESET}\n"
else
	@printf "${GREEN}"
	@printf " - No similar-named IP exists!\n"

# Create new IP directory

	@printf "${CYAN}"
	@printf "Creating starter IP\n"

	@$(VENV) && python tools/new-ip.py ${IP_NAME_PARSED}

# Make a new branch for the IP
	@printf "${CYAN}"
	@printf "Creating new IP branch...\n"
	
	@printf "${RESET}"
	@git checkout -b ${IP_NAME_PARSED}

	@printf "${CYAN}"
	@printf "Updating remote...\n"

	@printf "${RESET}"
	@git add .
	@git commit -m "Initial IP: ${IP_NAME_PARSED}"
	@git push --set-upstream origin ${IP_NAME_PARSED}

	@printf "${GREEN}"
	@printf "[SUCCESS] New IP successfully created!${RESET}\n"

endif

lint:
ifndef IP
	@tools/lint.sh
else
	@tools/lint.sh "./src/${IP}"
endif

test:
	@tools/test.sh ${EXTRA_ARGS}

# ------------------------------------------------------------------------------
# Testfloat generation
# Run
# ```
# make testfloat_gen FUNC=<func_name> EXTRA_ARGS=<extra_args>
# ```
# to generate testfloat data for a specific function.
# Files will be written to `build/testfloat_gen`
# ------------------------------------------------------------------------------
TESTFLOAT_DOCKER_IMAGE = $(shell docker build -q - < .docker/testfloat.Dockerfile)
OUTPUT_FILE="testfloat_gen"
BUILD_DIR="build"
testfloat_gen:
ifndef FUNC
	@printf "${RED}"
	@printf "[ERROR] No function specified! Please specify a function to generate testfloat data for using FUNC=<func_name>${RESET}\n"
	@exit 1
else
	@printf "${CYAN}"
	@printf "Generating testfloat data for ${FUNC}...${RESET}\n"
	@mkdir -p ${BUILD_DIR}
	@docker run --rm ${TESTFLOAT_DOCKER_IMAGE} \
		testfloat_gen ${FUNC} ${EXTRA_ARGS} > ${BUILD_DIR}/${OUTPUT_FILE}
	@printf "${GREEN}"
	@printf "[SUCCESS] Testfloat generation written to ${BUILD_DIR}/${OUTPUT_FILE}!${RESET}\n"
endif

# ------------------------------------------------------------------------------
# Caravel and flow stuff
# ------------------------------------------------------------------------------
# Create a docker container unique to a user and set it up
CARAVEL_DOCKER_IMAGE = $(shell docker build -q - < .docker/caravel.Dockerfile)
CARAVEL_DOCKER_CONTAINER = caravel-$(shell id -u)

force-install-caravel: caravel-remove-container install-caravel
caravel-remove-container:
	@docker rm -f ${CARAVEL_DOCKER_CONTAINER}
install-caravel:
	@if [ ! "$(shell docker ps -a -q -f name=${CARAVEL_DOCKER_CONTAINER})" ]; then \
		docker ps -a -q -f name=${CARAVEL_DOCKER_CONTAINER}; \
		printf "${CYAN}Setting up Caravel Docker container...${RESET}\n"; \
		docker run \
			--name ${CARAVEL_DOCKER_CONTAINER} \
			-v /var/run/docker.sock:/var/run/docker.sock \
			-v ${PWD}:/home/c2s2_ip:ro \
			-w /home/caravel_user_project \
			${CARAVEL_DOCKER_IMAGE} \
			make setup PWD=/home/caravel_user_project; \
	fi

# Run Caravel in an interactive docker shell
caravel:
ifndef PDK_ROOT
	@printf "${RED} [ERROR] PDK_ROOT environment variable not set!\n - Make sure you have sourced ${YELLOW}setup-c2s2.sh${RED}.${RESET}\n"
	@exit 1
endif
ifndef OPENLANE_ROOT
	@printf "${RED} [ERROR] OPENLANE_ROOT environment variable not set!\n - Make sure you have sourced ${YELLOW}setup-c2s2.sh${RED}.${RESET}\n"
	@exit 1
endif
	@docker exec -it \
		${CARAVEL_DOCKER_CONTAINER} bash

# ------------------------------------------------------------------------------
# Redundant rules to help with user typos
# ------------------------------------------------------------------------------
new_ip: new-ip
check_ip: check-ip
testfloat-gen: testfloat_gen