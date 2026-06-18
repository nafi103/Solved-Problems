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
    int n, m;
    cin >> n >> m;
    vector<vector<int>> grid(n, vector<int>(m));
    for(auto [i, c] = pair{0, '$'}; i < n; i++){
        for(int j = 0; j < m; j++){
            cin >> c;
            grid[i][j] = c - '0';
        }
    }
    int mn = 0, mx = 0;
    for(auto &arr: grid){
        int rem = m / 4, o = count(all(arr), 0ll), t = count(all(arr), 1ll);
        for(int i = 0; i < m - 1; i++){
            if(arr[i] == arr[i + 1] and arr[i] == 1){
                if(rem){
                    rem--;
                }else{
                    break;
                }
                t -= 2;
                mn++;
                i++;
            }
        }
        mn += t;
        int oo = 0; rem = m / 4;
        t = count(all(arr), 1ll);
        for(int i = 0; i < m - 1; i++){
            if(!(arr[i] == 1 and arr[i + 1] == 1) and rem){
                mx += (arr[i] + arr[i + 1]);
                rem--;
                t -= (arr[i] + arr[i + 1]);
                i++;
            }
        }
        if(rem)
            t -= rem;
        mx += t;
    }
    cout << mn << " " << mx << endl;
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