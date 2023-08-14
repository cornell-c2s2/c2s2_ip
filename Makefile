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
IP_USED = $(shell git branch -a | grep -cm 1 ${IP_NAME})

# Recipe for making new IP
new_ip:
	@echo -ne "${PURPLE}"
	@echo -e "========================================"
	@echo -e "C2S2 IP CREATOR"
	@echo -e "========================================\n"
	@echo -ne "${RESET}"

	@echo -ne "${CYAN}"
	@echo -e "Checking IP Name is set..."

ifndef IP_NAME
	@echo -ne "${RED}"
	@echo -e "[ERROR] Looks like you didn't specify a name for the IP!"
	@echo -e "[ERROR] Try running 'make new_ip IP_NAME=<name>'' instead,"
	@echo -e "[ERROR] replacing <name> with your desired IP name"
else
	
# Get name of IP
	@echo -ne "${GREEN}"
	@echo -e " - IP Name Set to ${IP_NAME}"

# Check if already used
	@echo -ne "${CYAN}"
	@echo -e "Checking previously-existing IP..."
ifeq (${IP_USED},1)
	@echo -ne "${RED}"
	@echo -e "[ERROR] A similar-named IP already exists!"
	@echo -e "[ERROR] Please choose a different name"
	@echo -e "[ERROR] (Use 'git branch -a' to see all of the existing"
	@echo -e "[ERROR] branches, corresponding to existing IP)"
else
	@echo -ne "${GREEN}"
	@echo -e " - No similar-named IP exists!"

# Make a new branch for the IP
	@echo -ne "${CYAN}"
	@echo -e "Creating new IP branch..."
	
	@echo -e "${RESET}"
	@git checkout -b ${IP_NAME}
	@echo -e ""

# Create new IP directory

	@echo -ne "${CYAN}"
	@echo -e "Creating starter IP"

	@mkdir ${IP_NAME}
	@touch ${IP_NAME}/${IP_NAME}.v
	@echo "//================================================" >> ${IP_NAME}/${IP_NAME}.v
	@echo "// ${IP_NAME}.v"                                    >> ${IP_NAME}/${IP_NAME}.v
	@echo "//================================================" >> ${IP_NAME}/${IP_NAME}.v
	@echo ""                                                   >> ${IP_NAME}/${IP_NAME}.v
	@echo "module ${IP_NAME}"                                  >> ${IP_NAME}/${IP_NAME}.v
	@echo "("                                                  >> ${IP_NAME}/${IP_NAME}.v
	@echo "  input  logic clk;"                                >> ${IP_NAME}/${IP_NAME}.v
	@echo "  input  logic q;"                                  >> ${IP_NAME}/${IP_NAME}.v
	@echo "  output logic d;"                                  >> ${IP_NAME}/${IP_NAME}.v
	@echo ");"                                                 >> ${IP_NAME}/${IP_NAME}.v
	@echo ""                                                   >> ${IP_NAME}/${IP_NAME}.v
	@echo "always_ff @( posedge clk )"                         >> ${IP_NAME}/${IP_NAME}.v
	@echo "  q <= d;"                                          >> ${IP_NAME}/${IP_NAME}.v
	@echo ""                                                   >> ${IP_NAME}/${IP_NAME}.v
	@echo "endmodule"                                          >> ${IP_NAME}/${IP_NAME}.v

	@echo -ne "${GREEN}"
	@echo -e " - Starter IP created at ${IP_NAME}/${IP_NAME}.v"

	@echo -ne "${CYAN}"
	@echo -e "Updating remote..."

	@echo -e "${RESET}"
	@git add .
	@git commit -m "Initial IP: ${IP_NAME}"
	@git push --set-upstream origin ${IP_NAME}

	@echo -ne "${GREEN}"
	@echo -e "[SUCCESS] New IP successfully created!"

endif
endif