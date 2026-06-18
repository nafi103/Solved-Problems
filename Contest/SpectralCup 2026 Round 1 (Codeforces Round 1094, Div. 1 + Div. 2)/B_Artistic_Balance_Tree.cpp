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
    int n, m, sum = 0;
    cin >> n >> m;
    vector<int> odd, even;
    for(int i = 1, x; i <= n; i++){
        cin >> x;
        if(i & 1)
            odd.push_back(x);
        else
            even.push_back(x);
        sum += x;
    }
    bool flag1 = true, flag2 = true;
    sort(all(even)); sort(all(odd));
    for(int i = 0, x; i < m; i++){
        cin >> x;
        if(x & 1){
            if(!odd.empty() and (odd.back() > 0 or flag1)){
                flag1 = false;
                sum -= odd.back();
                odd.pop_back();
            }
        }else{
            if(!even.empty() and (even.back() > 0 or flag2)){
                flag2 = false;
                sum -= even.back();
                even.pop_back();
            }
        }
    }
    cout << sum << endl;
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