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
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
int getRandomNumber(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);} 

int solve(int n, int k, string str)
{
    debug(n) debug(k) debug(str)
    // int n, k;
    // cin >> n >> k;
    // string str;
    // cin >> str;
    int score = 0;

    for (int i = 0; i < n; i++){
        if(str[i] == 'W'){
            score++;
            if(i and str[i - 1] == 'W')
                score++;
        }
    }

    if(n == 1){
        return (score or k ? 1 : 0);
        // cout << (score or k ? 1 : 0) << endl;
        // return;
    }

    int cnt = 0, cl = 0, cr = 0;
    int l = 0, r = n - 1;

    while(l < n and str[l] == 'L'){
        l++;
        cl++;
    }
    while(r >= 0 and str[r] == 'L'){
        r--;
        cr++;
    }

    if(l > r){
        return min(n * 2 - 1, k * 2 - 1);
        // cout << min(n * 2 - 1, k * 2 - 1) << endl;
        // return;
    }

    vector<int> pf;
    for (int i = l; i <= r; i++){
        if(str[i] == 'L')
            cnt++;
        else{
            if(cnt)
                pf.push_back(cnt);
            cnt = 0;
        }
    }

    sort(all(pf), greater<int>());

    while(!pf.empty() and k){
        int c = pf.back();
        pf.pop_back();
        if(c <= k){
            score += 2 * c + 1;
            k -= c;
        }else{
            score += k * 2;
            k = 0;
        }
    }

    if(cl and k){
        if(cl <= k){
            score += 2 * cl;
            k -= cl;
        }else{
            score += 2 * k;
            k = 0;
        }
    }
    if(cr and k){
        if(cr <= k){
            score += 2 * cr;
            k -= cr;
        }else{
            score += 2 * k;
            k = 0;
        }
    }
    // cout << min(n * 2 - 1, score) << endl;
    return min(n * 2 - 1, score);
}

int solve_bf(int n, int k, string str)
{
    debug(n) debug(k) debug(str)
    int score = 0;
    vector<int> pos;
    for (int i = 0; i < n; i++){
        if(str[i] == 'W'){
            score++;
            if(i and str[i - 1] == 'W')
                score++;
        }else{
            pos.push_back(i);
        }
    }
    debug(pos)
    if(k == 0){
        return score;
    }
    int r = (1 << sz(pos));
    for (int mask = 0; mask < r; mask++){
        if(__builtin_popcount(mask) <= k){
            string tmp = str;
            for (int j = 0; j < sz(pos); j++){
                if(mask & (1 << j))
                    tmp[pos[j]] = 'W';
            }
            debug(mask) debug(tmp)
            int score_tmp = 0;
            for (int i = 0; i < n; i++){
                if(tmp[i] == 'W'){
                    score_tmp++;
                    if (i and tmp[i - 1] == 'W')
                        score_tmp++;
                }
            }
            debug(score_tmp)
            score = max(score, score_tmp);
        }
    }
    return score;
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
        // int n, k;
        // string str;
        // cin >> n >> k >> str;
        int n = getRandomNumber(1, 10);
        int k = getRandomNumber(0, n);
        string str = "";
        for (int i = 0; i < n; i++){
            if(getRandomNumber(0, 1) == 0)
                str.push_back('L');
            else
                str.push_back('W');
        }
        int ans1 = solve(n, k, str);
        int ans2 = solve_bf(n, k, str);
        if (ans1 == ans2)
        {
            cout << "Passed" << endl;
        }
        else
        {
            cout << "Wrong: " << ans1 << endl;
            cout << "Correct: " << ans2 << endl;
            cout << n << " " << k << endl;
            cout << str << endl;
            break;
        }
        // solve(n, k, str);
    }
}