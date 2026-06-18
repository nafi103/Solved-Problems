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
    string str;
    cin >> str;
    int n = sz(str);
    vector<vector<int>> pref(n, vector<int> (26));
    vector<int> cnt(26, 0);
    for(int i = 0; i < n; i++){
        cnt[str[i] - 'a']++;
        pref[i] = cnt;
    }
    int q, l, r;
    cin >> q;
    while(q--){
        cin >> l >> r;
        if(l == r){
            cout << "Yes" << endl;
            continue;
        }
        r--, l--;
        if(str[r] != str[l])
            cout << "Yes" << endl;
        else{
            if(l == 0)
                cnt = pref[r];
            else{
                for(int i = 0; i < 26; i++){
                    cnt[i] = pref[r][i] - pref[l - 1][i];
                }
            }
            int distinct = 0;
            for(auto [i, c] = pair{0, 'a'}; i < 26; i++, c++){
                if(c == str[l])
                    continue;
                if(cnt[i] > 0)
                    distinct++;
            }
            if(distinct > 1)
                cout << "Yes" << endl;
            else
                cout << "No" << endl;
        }
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}