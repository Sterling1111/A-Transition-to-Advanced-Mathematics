Sums.vo Sums.glob Sums.v.beautified Sums.required_vo: Sums.v 
Sums.vio: Sums.v 
Sums.vos Sums.vok Sums.required_vos: Sums.v 
Complex.vo Complex.glob Complex.v.beautified Complex.required_vo: Complex.v 
Complex.vio: Complex.v 
Complex.vos Complex.vok Complex.required_vos: Complex.v 
WI_SI_WO.vo WI_SI_WO.glob WI_SI_WO.v.beautified WI_SI_WO.required_vo: WI_SI_WO.v 
WI_SI_WO.vio: WI_SI_WO.v 
WI_SI_WO.vos WI_SI_WO.vok WI_SI_WO.required_vos: WI_SI_WO.v 
QRT.vo QRT.glob QRT.v.beautified QRT.required_vo: QRT.v WI_SI_WO.vo
QRT.vio: QRT.v WI_SI_WO.vio
QRT.vos QRT.vok QRT.required_vos: QRT.v WI_SI_WO.vos
Fibonacci.vo Fibonacci.glob Fibonacci.v.beautified Fibonacci.required_vo: Fibonacci.v 
Fibonacci.vio: Fibonacci.v 
Fibonacci.vos Fibonacci.vok Fibonacci.required_vos: Fibonacci.v 
Sets.vo Sets.glob Sets.v.beautified Sets.required_vo: Sets.v Binomial.vo
Sets.vio: Sets.v Binomial.vio
Sets.vos Sets.vok Sets.required_vos: Sets.v Binomial.vos
Binomial.vo Binomial.glob Binomial.v.beautified Binomial.required_vo: Binomial.v Sums.vo
Binomial.vio: Binomial.v Sums.vio
Binomial.vos Binomial.vok Binomial.required_vos: Binomial.v Sums.vos
Chapter6.vo Chapter6.glob Chapter6.v.beautified Chapter6.required_vo: Chapter6.v Complex.vo
Chapter6.vio: Chapter6.v Complex.vio
Chapter6.vos Chapter6.vok Chapter6.required_vos: Chapter6.v Complex.vos
Chapter7.vo Chapter7.glob Chapter7.v.beautified Chapter7.required_vo: Chapter7.v Chapter6.vo
Chapter7.vio: Chapter7.v Chapter6.vio
Chapter7.vos Chapter7.vok Chapter7.required_vos: Chapter7.v Chapter6.vos
Chapter8.vo Chapter8.glob Chapter8.v.beautified Chapter8.required_vo: Chapter8.v QRT.vo Chapter7.vo
Chapter8.vio: Chapter8.v QRT.vio Chapter7.vio
Chapter8.vos Chapter8.vok Chapter8.required_vos: Chapter8.v QRT.vos Chapter7.vos
Chapter9.vo Chapter9.glob Chapter9.v.beautified Chapter9.required_vo: Chapter9.v QRT.vo Chapter8.vo
Chapter9.vio: Chapter9.v QRT.vio Chapter8.vio
Chapter9.vos Chapter9.vok Chapter9.required_vos: Chapter9.v QRT.vos Chapter8.vos
Chapter10.vo Chapter10.glob Chapter10.v.beautified Chapter10.required_vo: Chapter10.v Sets.vo Chapter9.vo
Chapter10.vio: Chapter10.v Sets.vio Chapter9.vio
Chapter10.vos Chapter10.vok Chapter10.required_vos: Chapter10.v Sets.vos Chapter9.vos
Chapter11.vo Chapter11.glob Chapter11.v.beautified Chapter11.required_vo: Chapter11.v Chapter10.vo
Chapter11.vio: Chapter11.v Chapter10.vio
Chapter11.vos Chapter11.vok Chapter11.required_vos: Chapter11.v Chapter10.vos
Chapter12.vo Chapter12.glob Chapter12.v.beautified Chapter12.required_vo: Chapter12.v Sets.vo Chapter11.vo
Chapter12.vio: Chapter12.v Sets.vio Chapter11.vio
Chapter12.vos Chapter12.vok Chapter12.required_vos: Chapter12.v Sets.vos Chapter11.vos
Chapter13.vo Chapter13.glob Chapter13.v.beautified Chapter13.required_vo: Chapter13.v Sums.vo Sets.vo WI_SI_WO.vo Chapter12.vo
Chapter13.vio: Chapter13.v Sums.vio Sets.vio WI_SI_WO.vio Chapter12.vio
Chapter13.vos Chapter13.vok Chapter13.required_vos: Chapter13.v Sums.vos Sets.vos WI_SI_WO.vos Chapter12.vos
Chapter14.vo Chapter14.glob Chapter14.v.beautified Chapter14.required_vo: Chapter14.v Fibonacci.vo Sums.vo Sets.vo Chapter13.vo
Chapter14.vio: Chapter14.v Fibonacci.vio Sums.vio Sets.vio Chapter13.vio
Chapter14.vos Chapter14.vok Chapter14.required_vos: Chapter14.v Fibonacci.vos Sums.vos Sets.vos Chapter13.vos
Chapter15.vo Chapter15.glob Chapter15.v.beautified Chapter15.required_vo: Chapter15.v Fibonacci.vo Sums.vo Sets.vo WI_SI_WO.vo Chapter14.vo
Chapter15.vio: Chapter15.v Fibonacci.vio Sums.vio Sets.vio WI_SI_WO.vio Chapter14.vio
Chapter15.vos Chapter15.vok Chapter15.required_vos: Chapter15.v Fibonacci.vos Sums.vos Sets.vos WI_SI_WO.vos Chapter14.vos
Chapter16.vo Chapter16.glob Chapter16.v.beautified Chapter16.required_vo: Chapter16.v Fibonacci.vo Sums.vo Sets.vo Binomial.vo Chapter15.vo
Chapter16.vio: Chapter16.v Fibonacci.vio Sums.vio Sets.vio Binomial.vio Chapter15.vio
Chapter16.vos Chapter16.vok Chapter16.required_vos: Chapter16.v Fibonacci.vos Sums.vos Sets.vos Binomial.vos Chapter15.vos
