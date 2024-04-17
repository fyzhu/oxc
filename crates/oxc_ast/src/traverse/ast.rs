#![allow(dead_code)] // just for now
use crate::ast;
use oxc_allocator::Allocator;

/// AST builder for creating AST nodes for traversable AST
pub struct TraversableAstBuilder<'a> {
    pub allocator: &'a Allocator,
}

impl<'a> TraversableAstBuilder<'a> {
    pub fn new(allocator: &'a Allocator) -> Self {
        Self { allocator }
    }
}

pub use ast::traversable_accessorproperty::*;
pub use ast::traversable_argument::*;
pub use ast::traversable_arrayassignmenttarget::*;
pub use ast::traversable_arrayexpression::*;
pub use ast::traversable_arrayexpressionelement::*;
pub use ast::traversable_arraypattern::*;
pub use ast::traversable_arrowfunctionexpression::*;
pub use ast::traversable_assignmentexpression::*;
pub use ast::traversable_assignmentpattern::*;
pub use ast::traversable_assignmenttarget::*;
pub use ast::traversable_assignmenttargetmaybedefault::*;
pub use ast::traversable_assignmenttargetpattern::*;
pub use ast::traversable_assignmenttargetproperty::*;
pub use ast::traversable_assignmenttargetpropertyidentifier::*;
pub use ast::traversable_assignmenttargetpropertyproperty::*;
pub use ast::traversable_assignmenttargetrest::*;
pub use ast::traversable_assignmenttargetwithdefault::*;
pub use ast::traversable_awaitexpression::*;
pub use ast::traversable_bigintliteral::*;
pub use ast::traversable_binaryexpression::*;
pub use ast::traversable_bindingidentifier::*;
pub use ast::traversable_bindingpattern::*;
pub use ast::traversable_bindingpatternkind::*;
pub use ast::traversable_bindingproperty::*;
pub use ast::traversable_bindingrestelement::*;
pub use ast::traversable_blockstatement::*;
pub use ast::traversable_breakstatement::*;
pub use ast::traversable_callexpression::*;
pub use ast::traversable_catchclause::*;
pub use ast::traversable_catchparameter::*;
pub use ast::traversable_chainelement::*;
pub use ast::traversable_chainexpression::*;
pub use ast::traversable_class::*;
pub use ast::traversable_classbody::*;
pub use ast::traversable_classelement::*;
pub use ast::traversable_computedmemberexpression::*;
pub use ast::traversable_conditionalexpression::*;
pub use ast::traversable_continuestatement::*;
pub use ast::traversable_declaration::*;
pub use ast::traversable_decorator::*;
pub use ast::traversable_directive::*;
pub use ast::traversable_dowhilestatement::*;
pub use ast::traversable_exportalldeclaration::*;
pub use ast::traversable_exportdefaultdeclaration::*;
pub use ast::traversable_exportdefaultdeclarationkind::*;
pub use ast::traversable_exportnameddeclaration::*;
pub use ast::traversable_exportspecifier::*;
pub use ast::traversable_expression::*;
pub use ast::traversable_expressionstatement::*;
pub use ast::traversable_forinstatement::*;
pub use ast::traversable_formalparameter::*;
pub use ast::traversable_formalparameters::*;
pub use ast::traversable_forofstatement::*;
pub use ast::traversable_forstatement::*;
pub use ast::traversable_forstatementinit::*;
pub use ast::traversable_forstatementleft::*;
pub use ast::traversable_function::*;
pub use ast::traversable_functionbody::*;
pub use ast::traversable_hashbang::*;
pub use ast::traversable_identifiername::*;
pub use ast::traversable_identifierreference::*;
pub use ast::traversable_ifstatement::*;
pub use ast::traversable_importattribute::*;
pub use ast::traversable_importattributekey::*;
pub use ast::traversable_importdeclaration::*;
pub use ast::traversable_importdeclarationspecifier::*;
pub use ast::traversable_importdefaultspecifier::*;
pub use ast::traversable_importexpression::*;
pub use ast::traversable_importnamespacespecifier::*;
pub use ast::traversable_importspecifier::*;
pub use ast::traversable_jsdocnullabletype::*;
pub use ast::traversable_jsxattribute::*;
pub use ast::traversable_jsxattributeitem::*;
pub use ast::traversable_jsxattributename::*;
pub use ast::traversable_jsxattributevalue::*;
pub use ast::traversable_jsxchild::*;
pub use ast::traversable_jsxclosingelement::*;
pub use ast::traversable_jsxelement::*;
pub use ast::traversable_jsxelementname::*;
pub use ast::traversable_jsxemptyexpression::*;
pub use ast::traversable_jsxexpression::*;
pub use ast::traversable_jsxexpressioncontainer::*;
pub use ast::traversable_jsxfragment::*;
pub use ast::traversable_jsxidentifier::*;
pub use ast::traversable_jsxmemberexpression::*;
pub use ast::traversable_jsxmemberexpressionobject::*;
pub use ast::traversable_jsxnamespacedname::*;
pub use ast::traversable_jsxopeningelement::*;
pub use ast::traversable_jsxspreadattribute::*;
pub use ast::traversable_jsxspreadchild::*;
pub use ast::traversable_jsxtext::*;
pub use ast::traversable_labeledstatement::*;
pub use ast::traversable_labelidentifier::*;
pub use ast::traversable_logicalexpression::*;
pub use ast::traversable_memberexpression::*;
pub use ast::traversable_metaproperty::*;
pub use ast::traversable_methoddefinition::*;
pub use ast::traversable_modifiers::*;
pub use ast::traversable_moduledeclaration::*;
pub use ast::traversable_moduleexportname::*;
pub use ast::traversable_newexpression::*;
pub use ast::traversable_numericliteral::*;
pub use ast::traversable_objectassignmenttarget::*;
pub use ast::traversable_objectexpression::*;
pub use ast::traversable_objectpattern::*;
pub use ast::traversable_objectproperty::*;
pub use ast::traversable_objectpropertykind::*;
pub use ast::traversable_parenthesizedexpression::*;
pub use ast::traversable_privatefieldexpression::*;
pub use ast::traversable_privateidentifier::*;
pub use ast::traversable_privateinexpression::*;
pub use ast::traversable_propertydefinition::*;
pub use ast::traversable_propertykey::*;
pub use ast::traversable_regexp::*;
pub use ast::traversable_regexpliteral::*;
pub use ast::traversable_returnstatement::*;
pub use ast::traversable_sequenceexpression::*;
pub use ast::traversable_simpleassignmenttarget::*;
pub use ast::traversable_spreadelement::*;
pub use ast::traversable_statement::*;
pub use ast::traversable_staticblock::*;
pub use ast::traversable_staticmemberexpression::*;
pub use ast::traversable_stringliteral::*;
pub use ast::traversable_switchcase::*;
pub use ast::traversable_switchstatement::*;
pub use ast::traversable_taggedtemplateexpression::*;
pub use ast::traversable_templateelement::*;
pub use ast::traversable_templateelementvalue::*;
pub use ast::traversable_templateliteral::*;
pub use ast::traversable_throwstatement::*;
pub use ast::traversable_trystatement::*;
pub use ast::traversable_tsarraytype::*;
pub use ast::traversable_tsasexpression::*;
pub use ast::traversable_tscallsignaturedeclaration::*;
pub use ast::traversable_tsclassimplements::*;
pub use ast::traversable_tsconditionaltype::*;
pub use ast::traversable_tsconstructortype::*;
pub use ast::traversable_tsconstructsignaturedeclaration::*;
pub use ast::traversable_tsenumdeclaration::*;
pub use ast::traversable_tsenummember::*;
pub use ast::traversable_tsenummembername::*;
pub use ast::traversable_tsexportassignment::*;
pub use ast::traversable_tsexternalmodulereference::*;
pub use ast::traversable_tsfunctiontype::*;
pub use ast::traversable_tsimportattribute::*;
pub use ast::traversable_tsimportattributename::*;
pub use ast::traversable_tsimportattributes::*;
pub use ast::traversable_tsimportequalsdeclaration::*;
pub use ast::traversable_tsimporttype::*;
pub use ast::traversable_tsindexedaccesstype::*;
pub use ast::traversable_tsindexsignature::*;
pub use ast::traversable_tsindexsignaturename::*;
pub use ast::traversable_tsinfertype::*;
pub use ast::traversable_tsinstantiationexpression::*;
pub use ast::traversable_tsinterfacebody::*;
pub use ast::traversable_tsinterfacedeclaration::*;
pub use ast::traversable_tsinterfaceheritage::*;
pub use ast::traversable_tsintersectiontype::*;
pub use ast::traversable_tsliteral::*;
pub use ast::traversable_tsliteraltype::*;
pub use ast::traversable_tsmappedtype::*;
pub use ast::traversable_tsmethodsignature::*;
pub use ast::traversable_tsmoduleblock::*;
pub use ast::traversable_tsmoduledeclaration::*;
pub use ast::traversable_tsmoduledeclarationbody::*;
pub use ast::traversable_tsmoduledeclarationname::*;
pub use ast::traversable_tsmodulereference::*;
pub use ast::traversable_tsnamedtuplemember::*;
pub use ast::traversable_tsnamespaceexportdeclaration::*;
pub use ast::traversable_tsnonnullexpression::*;
pub use ast::traversable_tsoptionaltype::*;
pub use ast::traversable_tspropertysignature::*;
pub use ast::traversable_tsqualifiedname::*;
pub use ast::traversable_tsresttype::*;
pub use ast::traversable_tssatisfiesexpression::*;
pub use ast::traversable_tssignature::*;
pub use ast::traversable_tstemplateliteraltype::*;
pub use ast::traversable_tsthisparameter::*;
pub use ast::traversable_tstupleelement::*;
pub use ast::traversable_tstupletype::*;
pub use ast::traversable_tstype::*;
pub use ast::traversable_tstypealiasdeclaration::*;
pub use ast::traversable_tstypeannotation::*;
pub use ast::traversable_tstypeassertion::*;
pub use ast::traversable_tstypeliteral::*;
pub use ast::traversable_tstypename::*;
pub use ast::traversable_tstypeoperator::*;
pub use ast::traversable_tstypeparameter::*;
pub use ast::traversable_tstypeparameterdeclaration::*;
pub use ast::traversable_tstypeparameterinstantiation::*;
pub use ast::traversable_tstypepredicate::*;
pub use ast::traversable_tstypepredicatename::*;
pub use ast::traversable_tstypequery::*;
pub use ast::traversable_tstypequeryexprname::*;
pub use ast::traversable_tstypereference::*;
pub use ast::traversable_tsuniontype::*;
pub use ast::traversable_unaryexpression::*;
pub use ast::traversable_updateexpression::*;
pub use ast::traversable_usingdeclaration::*;
pub use ast::traversable_variabledeclaration::*;
pub use ast::traversable_variabledeclarator::*;
pub use ast::traversable_whilestatement::*;
pub use ast::traversable_withclause::*;
pub use ast::traversable_withstatement::*;
pub use ast::traversable_yieldexpression::*;
