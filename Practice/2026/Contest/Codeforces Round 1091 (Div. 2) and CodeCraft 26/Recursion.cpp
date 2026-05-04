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

void solve(){
    int n, m;
    cin >> n >> m;
    if(n == 1){
        cout << (m == 1) << endl;
        return;
    }
    if(n < 1e9 + 2){
        m = (m - 1) % (n * n - 1) + 1;
    }
    int i = (m + n - 1) / n;
    int j = (m - 1) % n + 1;
    if(((i + j - 1) & j) == j)
        cout << 1 << endl;
    else
        cout << 0 << endl; 
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