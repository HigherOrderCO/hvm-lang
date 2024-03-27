// `Foo` inside the term `{Foo Foo}` is not in a active position, tests that it is not unnecessarily extracted
Foo = @a switch a { 0: {Foo Foo}; _: @* a-1 }

main = (Foo 0)
