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

int n, k;
string str;
vector<int> cnt(26);

bool check(vector<int> &cnt, int rem){
    for(auto &x: cnt){
        rem -= (k - (x % k)) % k;
    }
    return rem >= 0;
}

void solve()
{
    cin >> n >> k;
    cin >> str;
    if(n % k != 0){
        cout << -1 << endl;
        return;
    }
    fill(all(cnt), 0ll);
    for(auto &c: str){
        cnt[c - 'a']++;
    }
    bool flag = true;
    for(auto &x: cnt){
        if(x % k != 0){
            flag = false;
            break;
        }
    }
    if(flag){
        cout << str << endl;
        return;
    }
    int id = -1;
    for(int i = n - 1; i >= 0; i--){
        cnt[str[i] - 'a']--;
        for(int j = (str[i] - 'a') + 1; j < 26; j++){
            cnt[j]++;
            if(check(cnt, n - 1 - i)){
                str[i] = (char)('a' + j);
                id = i + 1;
                break;
            }
            cnt[j]--;
        }
        if(id != -1)
            break;
    }
    while(sz(str) > id)
        str.pop_back();
    int rem = n - id;
    for(int i = 25; i >= 0; i--){
        if(i == 0){
            str += string(rem, 'a');
        }else{
            int need = (k - (cnt[i] % k)) % k;
            if(need){
                str += string(need, (char)('a' + i));
            }
            rem -= need;
        }
    }
    reverse(str.begin() + id, str.end());
    cout << str << endl;
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