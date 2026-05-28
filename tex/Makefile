# Makefile for LaTeX compilation

# ターゲットとなるファイル名（拡張子なし）
TARGET = compilation_flow

# 使用するコンパイラとオプション
TEX = pdflatex
TEXFLAGS = -interaction=nonstopmode

.PHONY: all clean pdf

# デフォルトターゲット
all: pdf

# PDFの生成
pdf: $(TARGET).pdf

$(TARGET).pdf: $(TARGET).tex
	$(TEX) $(TEXFLAGS) $(TARGET).tex
	# 2回実行することで、相互参照や図の位置を正しく調整します
	$(TEX) $(TEXFLAGS) $(TARGET).tex

# 生成された中間ファイルとPDFの削除
clean:
	rm -f $(TARGET).aux $(TARGET).log $(TARGET).pdf $(TARGET).out $(TARGET).toc $(TARGET).nav $(TARGET).snm