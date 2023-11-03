Class {
	#name : #TqRecursiveEvaluator,
	#superclass : #TqEvaluator,
	#category : #'Tuqui-Evaluation-Runtime'
}

{ #category : #visiting }
TqRecursiveEvaluator >> evalMethodStatements: statements [
	| last result |
	last := nil.
	statements do: [ :node |
	last := node.
	result := node acceptVisitor: self ].

	^ (last notNil and: [ last isReturn ])
		ifTrue: [ result ]
 		ifFalse: [ self context receiver]
]

{ #category : #visiting }
TqRecursiveEvaluator >> evalPrimitive: aMethod [
	^(self primitiveFor: aMethod pragma name) value.
	
]

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateClosure: receiver whileFalse: arg [
	| result |
	[ result := self evaluateClosure: receiver.
	self booleanFrom: result ]
		whileFalse: [ self evaluateClosure: arg ].
	^ receiver
]

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateClosure: receiver whileTrue: arg [
	| result |
	[ result := self evaluateClosure: receiver.
	self booleanFrom: result ] whileTrue: [ self evaluateClosure: arg ].
	^ receiver
]

{ #category : #private }
TqRecursiveEvaluator >> evaluateClosure: closure withArgs: arguments [
	| block sblock receiver result |
	block := runtime closureBlock: closure.
	sblock := runtime blockExecutableCode: block.
	receiver := (runtime blockCapturesSelf: block)
		            ifTrue: [ closure at: 1 ]
		            ifFalse: [ nilObj ].
	context := TqRecursiveLinkedContext new
		runtime: runtime;
		beBlock;
		parent: context;
		self: receiver;
		initializeForBlock: sblock args: arguments closure: closure.
	result := nilObj.
	sblock statements do: [ :node | result := node acceptVisitor: self ].
	^ result
]

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateSend: symbol to: receiver with: anArray [

	^self
		       send: symbol
		       to: receiver
		       with: anArray
		       super: false
]

{ #category : #visiting }
TqRecursiveEvaluator >> hasFinished [
	^context isNil
]

{ #category : #visiting }
TqRecursiveEvaluator >> initializePrimitives [ 
	super initializePrimitives.
	primitives 
		at: #ClosureWhileTrue put: self primitiveClosureWhileTrue;
		at: #ClosureWhileFalse put: self primitiveClosureWhileFalse
]

{ #category : #visiting }
TqRecursiveEvaluator >> primitiveClosureWhileFalse [
	^ [ self
		evaluateClosure: context self
		whileFalse: context arguments first ]
]

{ #category : #visiting }
TqRecursiveEvaluator >> primitiveClosureWhileTrue [
	^ [ self
		evaluateClosure: context self
		whileTrue: context arguments first ]
]

{ #category : #visiting }
TqRecursiveEvaluator >> send: aSymbol to: receiver with: arguments super: aBoolean [

	| behavior method environment size |
	behavior := aBoolean
		            ifTrue: [ runtime superBehaviorOf: context classBinding ]
		            ifFalse: [ runtime behaviorOf: receiver ].
	method := self runtime doLookup: aSymbol startingAt: behavior.

	method isBlock ifTrue: [ ^ method value: receiver value: arguments ].
	method ifNil: [
		^ (undermessages at: aSymbol) value: receiver value: arguments ].
	self ASSERT: method notNil.
	size := runtime methodEnvironmentSize: method.
	environment := runtime newEnvironmentSized: size.
	context := TqRecursiveLinkedContext new
		           runtime: runtime;
		           self: receiver;
		           arguments: arguments;
		           environment: environment;
		           parent: context;
		           method: method.
	^ context evaluateFor: self
]

{ #category : #visiting }
TqRecursiveEvaluator >> send: aSymbol to: receiver with: arguments super: aBoolean sendSite: anSMessage [

	| behavior method environment size |
	behavior := aBoolean
		            ifTrue: [ runtime superBehaviorOf: context classBinding ]
		            ifFalse: [ runtime behaviorOf: receiver ].
	method := self
		          lookup: aSymbol
		          startingAt: behavior
		          sendSite: anSMessage.
	method isBlock ifTrue: [ ^ method value: receiver value: arguments ].
	self ASSERT: method notNil.
	size := runtime methodEnvironmentSize: method.
	environment := runtime newEnvironmentSized: size.
	context := TqRecursiveLinkedContext new
		           runtime: runtime;
		           self: receiver;
		           arguments: arguments;
		           environment: environment;
		           parent: context;
		           method: method.
	^ context evaluateFor: self
]

{ #category : #visiting }
TqRecursiveEvaluator >> superBehaviorOf: class [

	| superclass |
	superclass := self speciesSuperclass: class.
	^ self speciesInstanceBehavior: superclass
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitAssignment: anAssignment [
	| value |
 	value := anAssignment expression acceptVisitor: self.
	anAssignment assignees do: [ :assignee | 
		assignee binding assign: value within: self context.
		 ].
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitBlock: aBlock [
	^self context captureClosure: aBlock.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitIdentifier: anIdent [
 ^anIdent binding valueWithin: self context.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitLiteral: aLiteral [
	^aLiteral value.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitMessage: aMessage [
 | receiver args |
	receiver := aMessage receiver acceptVisitor: self.
	args := aMessage arguments collect: [:arg |
	arg acceptVisitor: self].
	^self send: (aMessage selector) to: receiver with: args super: false. 

]

{ #category : #visiting }
TqRecursiveEvaluator >> visitMethod: aMethod [

	^ aMethod pragma
		  ifNil: [ self evalMethodStatements: aMethod statements ]
		  ifNotNil: [ self evalPrimitive: aMethod ]
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitNonLocalReturn: aValue [
	^self context homeContext nonLocalReturn: aValue.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitReturn: aReturn [
	| value |
	
	value := aReturn expression acceptVisitor: self.
	aReturn local ifFalse: [^self visitNonLocalReturn: value].
	^value.

]
