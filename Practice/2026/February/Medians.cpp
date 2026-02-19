#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/


int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(3);
    cout.setf(ios::fixed);
    double a, b, c;
    while(cin >> a >> b >> c){
        double s = (a + b + c) / 2;
        double d = s * (s - a) * (s - b) * (s - c);
        if(d <= 0){
            cout << (double)-1 << endl;
        }else{
            cout << (4.0 / 3.0) * sqrt(d) << endl;
        }
    }
}