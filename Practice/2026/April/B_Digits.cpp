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

int fact(int n){
    if(n == 0)
        return 1;
    return n * fact(n - 1);
}

void solve()
{
    int n, d;
    cin >> n >> d;
    cout << 1;
    if(d == 3 or n >= 3 or d % 3 == 0)
        cout << " 3";
    if(d == 5)
        cout << " 5";
    if(n >= 3 or d == 7)
        cout << " 7";
    if(d == 9 or n >= 6 or (fact(n) * d) % 9 == 0)
        cout << " 9";
    cout << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}