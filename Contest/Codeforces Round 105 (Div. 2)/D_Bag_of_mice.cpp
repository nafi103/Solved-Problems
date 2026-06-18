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
    int W, B;
    cin >> W >> B;
    int rem = W + B;
    double dp[W + 1][B + 1][2][2];
    memset(dp, 0, sizeof dp);
    dp[W][B][0][0] = 1.0;
    for(int turn = 0; rem >= 0; turn++){
        for(int black_jump = 0; black_jump <= turn / 2; black_jump++){
            int white_jump = turn / 2 - black_jump;
            int b = B - turn - black_jump, w = W - white_jump;
            if(w > W or b > B or w < 0 or b < 0 or w + b <= 0)
                continue;
            double wp = (double)w / (w + b), bp = (double)b / (w + b);
            if((turn & 1) == 0){
                if(w)
                    dp[w - 1][b][1][1] += wp * dp[w][b][0][0];
                if(b)
                    dp[w][b - 1][1][0] += bp * dp[w][b][0][0];
            }else{
                if(b){
                    if(b >= 2)
                        dp[w][b - 2][0][0] += dp[w][b][1][0] * bp * ((double)b - 1) / (w + b - 1);
                    if(w)
                        dp[w - 1][b - 1][0][0] += dp[w][b][1][0] * bp * ((double)w) / (w + b - 1);
                }
            }
        }
        if(turn & 1)
            rem -= 2;
        else
            rem--;
    }
    double ans = 0;
    for(int w = 0; w <= W; w++){
        for(int b = 0; b <= B; b++){
            ans += dp[w][b][1][1];
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