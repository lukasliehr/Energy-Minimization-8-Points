"""Strict stdlib audit of source-bound joint exponent/height correction reports."""
from fractions import Fraction as Q
from .af_io import require

HEIGHT_METHOD='exact_height_polynomial_Bernstein_with_complete_model_error'
ERROR_METHOD='complete_coordinate_error_box_plus_shared_Hermite_remainders_on_every_piece'
GAMMA_METHOD='weighted_Young_min_entrywise_hull_or_control_plus_error'
METRIC_METHOD='short_dyadic_left_metric_exact_congruence'
EXACT_CENTER_METHOD='translated_dyadic_low_jet_with_complete_absolute_tail'
HEIGHT_JET_DEGREE=8
HEIGHT_JET_BITS=320
METRIC_CENTER_BITS=128
COUNT_KEYS=('shared_target_remainder_generators','scalar_rational_evaluations','scalar_polynomial_evaluations',
            'scalar_denominator_evaluations','exact_coefficient_congruences',
            'sqrt2_polynomial_entries','congruence_tensor_images','congruence_tensor_entries',
            'integer_polynomial_contractions','exact_height_numerator_coefficients',
            'metric_difference_control_enclosures','metric_difference_piece_enclosures','metric_difference_matrix_products')


def validate_policy(policy,block_names):
    require(type(policy) is dict,'Malformed joint correction policy')
    for cell,value in policy.items():
        require(type(cell) is str and cell and type(value) is dict
                and set(value)=={'depth','exact_blocks'},'Malformed per-cell joint policy')
        require(type(value['depth']) is int and 0<=value['depth']<=8,
                'Invalid joint restriction depth')
        names=value['exact_blocks']
        require(type(names) is list and all(type(q) is str for q in names)
                and len(set(names))==len(names) and names==[q for q in block_names if q in names],
                'Invalid exact metric block policy')


def report_metadata(centered,policy):
    return dict(policy=policy,height_method=HEIGHT_METHOD,error_method=ERROR_METHOD,
                gamma_method=GAMMA_METHOD,metric_method=METRIC_METHOD if policy['exact_blocks'] else None,
                exact_center_method=EXACT_CENTER_METHOD if policy['exact_blocks'] else None,
                height_jet_degree=HEIGHT_JET_DEGREE if policy['exact_blocks'] else None,
                height_jet_bits=HEIGHT_JET_BITS if policy['exact_blocks'] else None,
                scalar_rational_evaluations=centered['distinct_rational_evaluations'],
                scalar_polynomial_evaluations=centered['distinct_polynomial_evaluations'],
                scalar_denominator_evaluations=centered['distinct_denominator_evaluations'],
                metric_center_bits=METRIC_CENTER_BITS if policy['exact_blocks'] else None,
                metric_difference_terms=0,
                metric_centers=centered['metric_centers'],
                **centered['direct_congruence_counts'],pieces=centered['pieces'])


def audit_metadata(report,policy,order,bounds,errors,typed_equal,exact_nonnegative_list,exact_interval):
    metadata=report.get('joint_correction_metadata')
    if policy is None:
        require(metadata is None,'Unexpected joint correction metadata')
        return {key:0 for key in ('joint_height_pieces','joint_Bernstein_controls',*COUNT_KEYS)}
    require(type(metadata) is dict and set(metadata)=={
        'policy','height_method','error_method','gamma_method','metric_method','exact_center_method','pieces',
        'metric_center_bits','metric_difference_terms','metric_centers','height_jet_degree','height_jet_bits',*COUNT_KEYS},
        'Wrong joint correction metadata fields')
    expected=dict(policy=policy,height_method=HEIGHT_METHOD,error_method=ERROR_METHOD,
                  gamma_method=GAMMA_METHOD,metric_method=METRIC_METHOD if policy['exact_blocks'] else None,
                  exact_center_method=EXACT_CENTER_METHOD if policy['exact_blocks'] else None,
                height_jet_degree=HEIGHT_JET_DEGREE if policy['exact_blocks'] else None,
                height_jet_bits=HEIGHT_JET_BITS if policy['exact_blocks'] else None,
                  metric_center_bits=METRIC_CENTER_BITS if policy['exact_blocks'] else None,
                  metric_difference_terms=0)
    require(all(typed_equal(metadata.get(key),value) for key,value in expected.items()),
            'Joint correction method or policy mismatch')
    require(all(type(metadata[key]) is int and 0<=metadata[key]<=10**12 for key in COUNT_KEYS),
            'Malformed joint correction arithmetic counts')
    require(metadata['shared_target_remainder_generators']==report['degree'],
            'Incomplete shared Hermite remainder directions')
    if not policy['exact_blocks']:
        require(all(metadata[key]==0 for key in COUNT_KEYS if key not in ('shared_target_remainder_generators','scalar_rational_evaluations','scalar_polynomial_evaluations','scalar_denominator_evaluations')),
                'Unselected exact congruence has arithmetic counts')
    require(metadata['exact_coefficient_congruences']==0,
            'Unexpected dense coefficient congruence')
    count=1<<policy['depth'];pieces=metadata['pieces']
    centers=metadata['metric_centers']
    require(type(centers) is list and len(centers)==len(policy['exact_blocks']),
            'Incomplete exact-metric center inventory')
    nonzero_metrics=0
    orders=dict(zip(report['block_names'],report['block_orders']))
    for name,center in zip(policy['exact_blocks'],centers):
        require(type(center) is dict and set(center)=={'block','order','center_bits','exact','center',
            'nonzero_difference','maximum_exact_difference'},'Wrong metric center fields')
        require(typed_equal(center['block'],name) and typed_equal(center['order'],orders[name])
                and typed_equal(center['center_bits'],METRIC_CENTER_BITS),'Incorrect metric center identity or precision')
        for key in ('exact','center'):
            sizes=center[key]
            require(type(sizes) is dict and set(sizes)=={'max_numerator_bits','max_denominator_bits'}
                    and all(type(value) is int and 0<=value<=10**9 for value in sizes.values())
                    and sizes['max_denominator_bits']>=1,'Malformed exact metric bit accounting')
        require(center['center']['max_denominator_bits']<=METRIC_CENTER_BITS+1,
                'Metric center exceeds fixed dyadic denominator')
        require(type(center['nonzero_difference']) is bool and type(center['maximum_exact_difference']) is str,
                'Malformed complete metric discrepancy')
        difference=Q(center['maximum_exact_difference'])
        require(difference==0 and center['nonzero_difference'] is False
                and center['exact']==center['center'],'Short left metric is not exact at declared precision')
        nonzero_metrics+=int(center['nonzero_difference'])
    enclosures=count*(order+1)*nonzero_metrics
    require(metadata['metric_difference_control_enclosures']==enclosures
            and metadata['metric_difference_piece_enclosures']==count*nonzero_metrics
            and metadata['metric_difference_matrix_products']==4*count*nonzero_metrics,
            'Incomplete three-term metric difference arithmetic')
    require(type(pieces) is list and len(pieces)==count,'Incomplete joint piece cover')
    global_lower,global_upper=exact_interval(report['root']['a_enclosure'],'global joint height')
    per_piece=[];per_error=[]
    def interval(value,label):
        require(type(value) is list and len(value)==2 and all(type(x) is str for x in value),
                'Malformed '+label)
        lo,hi=map(Q,value);require(lo<=hi,'Reversed '+label);return lo,hi
    for index,piece in enumerate(pieces):
        require(type(piece) is dict and set(piece)=={
            't_interval','height_interval','bounds','error_bounds','control_bounds','entrywise_bounds'},
            'Wrong joint piece fields')
        require(interval(piece['t_interval'],'joint exponent piece')==
                (Q(-1)+Q(2*index,count),Q(-1)+Q(2*(index+1),count)),
                'Incorrect closed dyadic piece cover')
        lo,hi=interval(piece['height_interval'],'joint height piece')
        require(global_lower<=lo<=hi<=global_upper,'Joint height leaves global enclosure')
        pb=exact_nonnegative_list(piece['bounds'],4,'joint piece bounds')
        pe=exact_nonnegative_list(piece['error_bounds'],4,'joint piece errors')
        pc=exact_nonnegative_list(piece['control_bounds'],4,'joint control gamma bounds')
        pm=exact_nonnegative_list(piece['entrywise_bounds'],4,'joint entrywise gamma bounds')
        require(all(b==min(m,c+e) and e<=b for b,m,c,e in zip(pb,pm,pc,pe)),
                'Incorrect joint gamma alternatives or error accounting')
        per_piece.append(pb);per_error.append(pe)
    require(bounds==[max(piece[j] for piece in per_piece) for j in range(4)]
            and errors==[max(piece[j] for piece in per_error) for j in range(4)],
            'Joint complete bounds do not equal maxima over all pieces')
    return dict(joint_height_pieces=count,joint_Bernstein_controls=count*(order+1),
                **{key:metadata[key] for key in COUNT_KEYS})
