//! Test Java language support.

use go_brrr::lang::java::Java;
use go_brrr::lang::traits::Language;

fn main() {
    let java = Java;

    // Test parsing
    let mut parser = java.parser().expect("Failed to create parser");

    let code = r#"
import java.util.List;
import static java.lang.Math.PI;

/**
 * User class with documentation.
 */
@Entity
public class User extends BaseEntity implements Serializable {
    private String name;

    /**
     * Constructor.
     */
    public User(String name) {
        this.name = name;
    }

    /**
     * Get name.
     */
    @Override
    public String getName() {
        return name;
    }

    public static <T> List<T> process(List<T> items, int count) {
        return items;
    }
}
"#;

    let tree = parser.parse(code, None).expect("Failed to parse");
    let root = tree.root_node();

    println!("=== Java Language Support Test ===\n");

    // Test import extraction
    let imports = java.extract_imports(&tree, code.as_bytes());
    println!("Imports found: {}", imports.len());
    for imp in &imports {
        println!(
            "  - {}{}",
            imp.module,
            if imp.is_from { " (static)" } else { "" }
        );
    }

    // Test class and method extraction
    for child in root.children(&mut root.walk()) {
        if child.kind() == "class_declaration" {
            if let Some(class) = java.extract_class(child, code.as_bytes()) {
                println!("\nClass: {}", class.name);
                println!("  Bases: {:?}", class.bases);
                println!("  Decorators: {:?}", class.decorators);
                if let Some(doc) = &class.docstring {
                    println!("  Doc: {}", doc.lines().next().unwrap_or(""));
                }
                println!("  Methods:");
                for method in &class.methods {
                    println!("    - {} ({})", method.name, method.signature());
                    println!("      Decorators: {:?}", method.decorators);
                }
            }
        }
    }

    println!("\n=== Test Passed ===");
}
