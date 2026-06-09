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

int C[32][32];

void solve()
{
    int n, k;
    cin >> n >> k;

    int msb = __builtin_ctz(n);

    if(k >= max(msb + 1, 2 * msb - 1)){
        cout << 0 << endl;
        return;
    }

    int ans = (msb + 1 > k);
    for(int i = msb - 1; i >= 0; i--){
        int op = i + 1;
        int l = max(0ll, k + 1 - op), r = i;

        if(l > r)
            break;

        for(int j = l; j <= r; j++){
            ans += C[i][j];
        }
    }

    cout << ans << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    C[0][0] = 1;
    for(int i = 1; i < 32; i++){
        for(int j = 0; j <= i; j++){
            C[i][j] += C[i - 1][j];
            if(j)
                C[i][j] += C[i - 1][j - 1];
        }
    }

    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}