SRC_DIR = src
BUILD_DIR = $(SRC_DIR)
SOURCE_FILES := ast.v asm.v dasm.v
BINARY_FILES := $(patsubst %.v,$(BUILD_DIR)/%.vo,$(SOURCE_FILES)) $(patsubst %.v,$(BUILD_DIR)/.%.vo.aux,$(SOURCE_FILES)) $(patsubst %.v,$(BUILD_DIR)/%.glob,$(SOURCE_FILES))
SOURCE_FILES := $(patsubst %,$(SRC_DIR)/%,$(SOURCE_FILES))

.PHONY: all
all: $(BINARY_FILES)

$(BUILD_DIR)/%.vo: $(SRC_DIR)/%.v | $(BUILD_DIR)
	coqtop -color yes -R $(SRC_DIR) "" -compile $<

$(BUILD_DIR):
	@mkdir -p $(BUILD_DIR)

clean:
	@rm $(BINARY_FILES) 2>/dev/null || true
