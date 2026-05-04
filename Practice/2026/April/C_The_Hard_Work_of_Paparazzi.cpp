#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e15 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 1e5 + 10;
int dp[N];
vector<array<int, 3>> celebrity(N);

void solve()
{
    int r, n, ans = 0, pref_max = -inf;
    cin >> r >> n;
    dp[0] = 0;
    celebrity[0] = {0, 1, 1};
    for (int i = 1, p = 0; i <= n; i++){
        auto &[t2, x2, y2] = celebrity[i];
        cin >> t2 >> x2 >> y2;
        while(t2 - celebrity[p][0] >= 2 * r){
            pref_max = max(pref_max, dp[p]);
            p++;
        }
        dp[i] = pref_max + 1;
        for (int j = i - 1; j >= p; j--){
            auto &[t1, x1, y1] = celebrity[j];
            if(abs(x1 - x2) + abs(y1 - y2) <= t2 - t1){
                dp[i] = max({dp[i], dp[j] + 1});
            }
        }
        ans = max(ans, dp[i]);
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
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}