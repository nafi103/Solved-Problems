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
 const int N = 2e5 + 10;
vector<pair<int,int>> elf(N);
int n, m, sum, mx, pref[N];
 void input(){
    sum = mx = 0;
    cin >> n >> m;
    for(int i = 0; i < n; i++){
        cin >> elf[i].first;
        sum += elf[i].first;
        mx = max(mx, elf[i].first);
        elf[i].second = i + 1;
    }
}
 void solve()
{
    input();
    if(2 * m > n or (m == 0 and 2 * mx > sum)){
        cout << -1 << endl;
        return;
    }
    vector<pair<int,int>> ans;
    sort(elf.begin(), elf.begin() + n);
    for(int i = 0; i < n; i++){
        pref[i] = elf[i].first;
        if(i)
            pref[i] += pref[i - 1];
    }
    if(m == 0){
        bool mode = 0;
        for(int i = 0; i < n - 1; i++){
            if(pref[n - 2] - (i ? pref[i - 1] : 0) >= elf[n - 1].first and 
                pref[n - 2] - pref[i] < elf[n - 1].first)
                mode = 1;
            if(mode){
                ans.emplace_back(elf[i].second, elf[n - 1].second);
            }else{
                ans.emplace_back(elf[i].second, elf[i + 1].second);
            }
        }
    }else{
        for(int i = 0; n - 1 - i >= 2 * m; i++){
            ans.emplace_back(elf[i].second, elf[i + 1].second);
        }
        for(int i = n - 2 * m, j = n - 1; i < j; i++, j--){
            ans.emplace_back(elf[j].second, elf[i].second);
        }
    }
    cout << sz(ans) << endl;
    for(auto &[x, y]: ans){
        cout << x << " " << y << endl;
    }
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