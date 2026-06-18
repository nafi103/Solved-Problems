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

int main()
{
    fastIO;
    int arr[27] = {0}, cnt = 0, pos = 26;
    string str;
    cin >> str;
    for (int i = 0; i < (int)str.size(); i++)
    {
        arr[(int)(str[i] - 'A')]++;
    }
    for (int i = 0; i < 26; i++)
    {
        if (arr[i] % 2 == 1)
        {
            pos = i;
            cnt++;
        }
        if (cnt > 1)
            break;
    }
    if (cnt > 1)
    {
        cout << "NO SOLUTION" << endl;
    }
    else
    {
        for (int i = 0; i < 26; i++)
        {
            if (arr[i] > 0 && i != pos)
            {
                int k = arr[i] / 2;
                for (int j = 1; j <= k; j++)
                {
                    cout << char((char(i) + 'A'));
                }
            }
        }
        for (int i = 1; i <= arr[pos]; i++)
        {
            cout << char(char(pos) + 'A');
        }
        for (int i = 25; i >= 0; i--)
        {
            if (arr[i] > 0 && i != pos)
            {
                int k = arr[i] / 2;
                for (int j = 1; j <= k; j++)
                {
                    cout << char((char(i) + 'A'));
                }
            }
        }
        cout << endl;
    }
}