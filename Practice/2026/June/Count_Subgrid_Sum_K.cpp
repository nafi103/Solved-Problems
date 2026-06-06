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
    char c;
    int n, m, k, ans = 0;
    cin >> n >> m >> k;

    vector<vector<int>> pref(n + 1, vector<int> (m + 1, 0));
    vector<int> cnt(n * m + 1, 0);
    cnt[0] = 1;

    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= m; j++){
            cin >> c;
            pref[i][j] = (c == '1');
            pref[i][j] += pref[i - 1][j];
            pref[i][j] += pref[i][j - 1];
            pref[i][j] -= pref[i - 1][j - 1];
        }
    }

    for(int r1 = 1; r1 <= n; r1++){
        for(int r2 = r1; r2 <= n; r2++){
            vector<int> ers;

            for(int w = 1; w <= m; w++){
                int psum = pref[r2][w] - pref[r1 - 1][w];
                ers.push_back(psum);
                if(psum >= k)
                    ans += cnt[psum - k];
                cnt[psum]++;
            }

            for(auto &x: ers)
                cnt[x] = 0;
            cnt[0] = 1;
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
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}