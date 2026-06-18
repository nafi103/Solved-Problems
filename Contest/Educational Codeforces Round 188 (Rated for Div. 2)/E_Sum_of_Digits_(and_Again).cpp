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
 int digit_sum(int x){
    int res = 0;
     while(x){
        res += x % 10;
        x /= 10;
    }
     return res;
}
 vector<int> get_target(int n){
    vector<int> cnt(10, 0);
     while(n > 9){
        int new_n = 0;
        while(n){
            cnt[n % 10]++;
            new_n += n % 10;
            n /= 10;
        }
        n = new_n;
    }
     cnt[n]++;
    return cnt;
}
 void solve()
{
    vector<int> cnt(10, 0);
    string str;
    cin >> str;
     if(sz(str) == 1){
        cout << str << endl;
        return;
    }
     int sum = 0;
    for(auto &c: str){
        cnt[c - '0']++;
        sum += (c - '0');
    }
     vector<bool> dp(sum + 1, false);
    dp[0] = true;
    for(int d = 1; d < 10; d++){
        int c = cnt[d];
        if(c == 0)
            continue;
         for(int j = 0; (1 << j) <= c; j++){
            int shift = (1 << j) * d;
            for(int k = sum; k >= shift; k--)
                dp[k] = dp[k] | dp[k - shift];
            c -= (1 << j);
        }
        int shift = c * d;
        for(int k = sum; k >= shift; k--)
            dp[k] = dp[k] | dp[k - shift];
    }
     for(int i = 1; i <= sum; i++){
        if(dp[i]){
            vector<int> need = get_target(i);
            vector<int> remaining = cnt;
             bool impossible = false;
            for(int j = 0; j < 10; j++){
                remaining[j] -= need[j];
                if(remaining[j] < 0){
                    impossible = true;
                    break;
                }
            }
             if(impossible)
                continue;
             int reach = 0;
            for(int j = 1; j < 10; j++)
                reach += j * remaining[j];
             if(reach == i){
                for(int j = 9; j >= 0; j--)
                    cout << string(remaining[j], (char)('0' + j));
            }else{
                continue;
            } 
             while(reach > 9){
                cout << reach;
                reach = digit_sum(reach);
            }
            cout << reach << endl;
            return;
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}