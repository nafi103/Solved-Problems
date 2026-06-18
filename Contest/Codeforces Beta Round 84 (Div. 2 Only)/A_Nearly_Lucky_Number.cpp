#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 int main()
{
    fastIO;
    string str;
    cin >> str;
    int n = str.size(), cnt = 0;
    bool flag = true;
    for (int i = 0; i < n; i++)
    {
        if (str[i] == '4' || str[i] == '7')
        {
            cnt++;
        }
    }
    int k = cnt;
    while (cnt > 0)
    {
        int k = cnt % 10;
        if (k == 4 || k == 7)
        {
            cnt /= 10;
        }
        else
        {
            flag = false;
            break;
        }
    }
    if (flag && k > 0)
        yes;
    else
        no;
}