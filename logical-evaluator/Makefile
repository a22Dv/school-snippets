TARGET = logeval

CXX = clang++
CXXFLAGS = -std=c++20 -stdlib=libc++ -Iinclude -O2
LLVM_LIB_PATH = /opt/llvm/lib/x86_64-unknown-linux-gnu
LDFLAGS = -L$(LLVM_LIB_PATH) -rpath $(LLVM_LIB_PATH)
SRCFILES = ./src/main.cpp ./src/lexer.cpp ./src/ast.cpp
all: ./src/main.cpp ./src/lexer.cpp ./src/ast.cpp
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $(SRCFILES) -o $(TARGET)
clean:
	rm $(TARGET)