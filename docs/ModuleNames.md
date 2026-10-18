# Test and example module names

Direct-import clients use the `SchemePropertiesTest` root; concrete examples
use `SchemePropertiesExamples`. Their source files are in
[`SchemePropertiesTest/`](../SchemePropertiesTest/) and
[`SchemePropertiesExamples/`](../SchemePropertiesExamples/).

For module names with the earlier generic roots, keep the suffix and replace
the root as follows:

| Earlier module name | Module name |
| --- | --- |
| `Test.<Module>` | `SchemePropertiesTest.<Module>` |
| `Examples.<Module>` | `SchemePropertiesExamples.<Module>` |

For example, use `import SchemePropertiesTest.ModuleTensorClient` or
`import SchemePropertiesExamples.ComponentScheme`. Namespaces and explicitly
named public declarations are unchanged. The library imports `SchemeProperties` and
`SchemeProperties.<Module>` are unchanged.

The [historical API reference](API.md) uses the earlier module names;
the table above gives their corresponding names in the current source tree.
