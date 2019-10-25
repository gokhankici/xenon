#ifndef IR_EXPR_H
#define IR_EXPR_H

#include <vector>
#include <string>

#include "Module.h"

// -----------------------------------------------------------------------------
// IR Expressions
// -----------------------------------------------------------------------------

/*
data IRExpr = Constant String
            | Variable String
            | UninterpretedFunction String [IRExpr]
            | IfThenElse IRExpr IRExpr IRExpr
            | String String
            | Select IRExpr List[IRExpr]
*/

class IRExpr
{
public:
    virtual std::ostream &print(std::ostream &) const = 0;
    std::string toIRString() const;
};

// constant
class IRExpr_Constant : public IRExpr
{
public:
    IRExpr_Constant(const std::string &c) : constant(c) {}
    std::ostream &print(std::ostream &) const;

private:
    const std::string constant;
};

// variable
class IRExpr_Variable : public IRExpr
{
public:
    IRExpr_Variable(const std::string &v, const Module* m) : variable(v), moduleName(m->mod_name().str()) {}
    IRExpr_Variable(const IRExpr_Variable &other) : variable(other.variable), moduleName(other.moduleName) {}

    std::ostream &print(std::ostream &) const;
    friend bool operator==(const IRExpr_Variable& v1, const IRExpr_Variable& v2);

    class Hash
    {
    public:
        size_t operator()(const IRExpr_Variable& v) const
        {
            return std::hash<std::string>()(v.variable) + 37 * std::hash<std::string>()(v.moduleName);
        }
    };

private:
    const std::string variable;
    const std::string moduleName;
};

// uninterpreted function
class IRExpr_UF : public IRExpr
{
public:
    IRExpr_UF(const char *f) : function(f) {}
    IRExpr_UF(const std::string &f) : function(f) {}
    IRExpr_UF(const char *f, const IRExpr *o) : function(f)
    {
        operands.push_back(o);
    }
    IRExpr_UF(const char *f, const IRExpr *o1, const IRExpr *o2) : function(f)
    {
        operands.push_back(o1);
        operands.push_back(o2);
    }
    IRExpr_UF(const IRExpr_UF &other) : function(other.function), operands(other.operands) {}
    void addOperand(const IRExpr *operand);
    std::ostream &print(std::ostream &) const;

private:
    const std::string function;
    std::vector<const IRExpr *> operands;
};

// Ternary if expression
class IRExpr_If : public IRExpr
{
public:
    IRExpr_If(const IRExpr *c, const IRExpr *t, const IRExpr *e)
        : condition(c), thenStmt(t), elseStmt(e)
    {
    }
    std::ostream &print(std::ostream &) const;

private:
    const IRExpr *const condition;
    const IRExpr *const thenStmt;
    const IRExpr *const elseStmt;
};

class IRExpr_String : public IRExpr
{
public:
    IRExpr_String(const std::string &v) : value(v) {}
    std::ostream &print(std::ostream &) const;

private:
    const std::string value;
};

// variable[i1][i2:i3][i4]...
class IRExpr_Select : public IRExpr
{
public:
    IRExpr_Select(const IRExpr_Variable *v) : variable(v) {}
    void addIndex(const IRExpr *i)
    {
        indices.push_back(i);
    }
    const IRExpr_Variable *getVariable() const
    {
        return variable;
    }
    const std::vector<const IRExpr *> &getIndices() const
    {
        return indices;
    }
    std::ostream &print(std::ostream &) const;

private:
    const IRExpr_Variable *const variable;
    std::vector<const IRExpr *> indices;
};

std::ostream &operator<<(std::ostream &, const IRExpr &);

#endif