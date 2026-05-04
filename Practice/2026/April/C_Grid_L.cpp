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

void solve()
{
    int p, q;
    cin >> p >> q;
    int sum = 2 * q + p, r = 4 * sqrt(sum);
    r = min(r, sum);
    for(int n = 1; n < r; n++){
        if((sum - n) % (2 * n + 1) == 0){
            int m = (sum - n) / (2 * n + 1), cover = max(n, m) - min(n, m);
            if(cover <= p){
                cout << n << " " << m << endl;
                return;
            }
        }
    }
    cout << -1 << endl;
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