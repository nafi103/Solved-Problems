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
    map<char,int> cnt;
    cin >> str;
    int n = sz(str);
    for(auto &x: str)
        cnt[x]++;
    string ans = "";
    for(int i = 0; i < n; i++){
        int m = n - i;
        char not_allowed = '$', take = '$';
        if(i)
            not_allowed = ans[i - 1];
        for(auto &[f,s]: cnt){
            if(s >= (m + 2) / 2){
                take = f;
                s--;
                break;
            }
        }
        if(take == '$'){
            for(auto &[f,s]: cnt){
                if(f != not_allowed){
                    s--;
                    take = f;
                    break;
                }
            }
        }
        if(take == '$' and take != not_allowed){
            cout << -1 << endl;
            return;
        }else{
            if(cnt[take] == 0)
                cnt.erase(take);
            ans.push_back(take);
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