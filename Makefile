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

# Check if our IP has already been used in a branch
IP_USED = $(shell git pull -q; git branch -a | grep -cm 1 ${IP_NAME})

# Recipe to check whether an IP already exists
check_ip:
	@printf "${CYAN}"
	@printf "Checking IP Name is set...\n"

ifndef IP_NAME
	@printf " ${RED}""
	@printf "[ERROR] Looks like you didn't specify a name for the IP!\n"
	@printf "[ERROR] Try running 'make new_ip IP_NAME=<name>'' instead,\n"
	@printf "[ERROR] replacing <name> with your desired IP name\n"

else
	@printf "${GREEN}"
	@printf " - IP Name Set to ${IP_NAME}\n"
	
	@printf "${CYAN}"
	@printf "Checking for IP names similar to %s...\n" ${IP_NAME}

ifeq (${IP_USED},1)
	@printf "${RED}"
	@printf "[ERROR] A similar-named IP already exists!\n"
	@printf "[ERROR] Please choose a different name\n"
	@printf "[ERROR] (Use 'git branch -a' to see all of the existing\n"
	@printf "[ERROR] branches, corresponding to existing IP)\n"

else
	@printf "${GREEN}"
	@printf " - No similar-named IP exists!\n"
endif
endif

# Recipe for making new IP
new_ip:
	@printf "${PURPLE}"
	@printf "========================================\n"
	@printf "C2S2 IP CREATOR\n"
	@printf "========================================\n"
	@printf "${RESET}"

	@printf "${CYAN}"
	@printf "Checking IP Name is set...\n"

ifndef IP_NAME
	@printf "${RED}"
	@printf "[ERROR] Looks like you didn't specify a name for the IP!\n"
	@printf "[ERROR] Try running 'make new_ip IP_NAME=<name>'' instead,\n"
	@printf "[ERROR] replacing <name> with your desired IP name\n"
else
	
# Get name of IP
	@printf "${GREEN}"
	@printf " - IP Name Set to ${IP_NAME}\n"

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

	@python tools/new_ip.py ${IP_NAME}

# Make a new branch for the IP
	@printf "${CYAN}"
	@printf "Creating new IP branch...\n"
	
	@printf "${RESET}"
	@git checkout -b ${IP_NAME}

	@printf "${CYAN}"
	@printf "Updating remote...\n"

	@printf "${RESET}"
	@git add .
	@git commit -m "Initial IP: ${IP_NAME}"
	@git push --set-upstream origin ${IP_NAME}

	@printf "${GREEN}"
	@printf "[SUCCESS] New IP successfully created!\n"

endif
endif
