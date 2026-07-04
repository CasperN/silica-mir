package tree_sitter_silica_mir_test

import (
	"testing"

	tree_sitter "github.com/smacker/go-tree-sitter"
	"github.com/tree-sitter/tree-sitter-silica_mir"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_silica_mir.Language())
	if language == nil {
		t.Errorf("Error loading SilicaMir grammar")
	}
}
