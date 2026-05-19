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

const int N = 5e5 + 10;
int a[N], b[N], a_id[N], b_id[N];
int dp[N][2];

void solve()
{
    int n;
    cin >> n;
    // vector<vector<int>> dp(n + 2, vector<int>(2, 0));
    for(int i = 0; i < n; i++){
        a_id[i + 1] = n;
        b_id[i + 1] = n;
        cin >> a[i];
    }

    a_id[n + 1] = n;
    b_id[n + 1] = n;

    for(int i = 0; i < n; i++){
        cin >> b[i];
    }
    
    int ans = 0;
    dp[n][0] = dp[n][1] = 0;
    for(int i = n - 1; i >= 0; i--){
        if(a[i] == b[i]){
            if(a[i] == 1){
                int a_2 = a_id[2], b_2 = b_id[2];
                if(a_2 != b_2){
                    dp[i][0] = min(a_2, b_2) - i;
                }else{
                    dp[i][0] = dp[a_2][1] + (a_2 - i);
                }
            }else{
                dp[i][0] = dp[i + 1][0] + 1;
            }
            int a_next = a_id[a[i] + 1], b_next = b_id[b[i] + 1];
            if(a_next != b_next){
                dp[i][1] = min(a_next, b_next) - i;
            }else{
                dp[i][1] = dp[a_next][1] + (a_next - i);
            }
        }else{
            if(a[i] == 1 or b[i] == 1){
                dp[i][0] = 0;
            }else{
                dp[i][0] = dp[i + 1][0] + 1;
            }
        }
        a_id[a[i]] = i;
        b_id[b[i]] = i;
        ans += dp[i][0];
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}