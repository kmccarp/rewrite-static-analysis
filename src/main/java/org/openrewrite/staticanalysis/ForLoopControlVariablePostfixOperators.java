/*
 * Copyright 2021 the original author or authors.
 * <p>
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * <p>
 * https://www.apache.org/licenses/LICENSE-2.0
 * <p>
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.openrewrite.staticanalysis;

import org.openrewrite.ExecutionContext;
import org.openrewrite.Recipe;
import org.openrewrite.TreeVisitor;
import org.openrewrite.internal.ListUtils;
import org.openrewrite.java.JavaIsoVisitor;
import org.openrewrite.java.tree.J;

public class ForLoopControlVariablePostfixOperators extends Recipe {
    @Override
    public String getDisplayName() {
        return "`for` loop counters should use postfix operators";
    }

    @Override
    public String getDescription() {
        return """
                Replace `for` loop control variables using pre-increment (`++i`) or pre-decrement (`--i`) operators \
                with their post-increment (`i++`) or post-decrement (`i++`) notation equivalents.\
                """;
    }

    @Override
    public TreeVisitor<?, ExecutionContext> getVisitor() {
        return new JavaIsoVisitor<ExecutionContext>() {
            @Override
            public J.ForLoop visitForLoop(J.ForLoop forLoop, ExecutionContext ctx) {
                forLoop = forLoop.withControl(
                        forLoop.getControl().withUpdate(
                                ListUtils.map(forLoop.getControl().getUpdate(), update -> {
                                    if (update instanceof J.Unary u) {
                                        if (u.getOperator() == J.Unary.Type.PreIncrement) {
                                            return u.withOperator(J.Unary.Type.PostIncrement);
                                        } else if (u.getOperator() == J.Unary.Type.PreDecrement) {
                                            return u.withOperator(J.Unary.Type.PostDecrement);
                                        }
                                    }

                                    return update;
                                })
                        )
                );

                return super.visitForLoop(forLoop, ctx);
            }
        };
    }

}
